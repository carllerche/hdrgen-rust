#![crate_id= "hdrgen#0.0.1"]

extern crate collections;
extern crate debug;
extern crate syntax;
extern crate rustc;

use std::cell::RefCell;
use std::io::Command;
use std::path::Path;
use std::rc::Rc;
use collections::{HashMap,HashSet};
use rustc::driver::{config,driver,session};
use rustc::metadata::creader::Loader;
use rustc::middle::{lint,ty};
use rustc::middle::typeck::{astconv,infer};
use syntax::codemap::Span;
use syntax::crateid::CrateId;
use syntax::parse::token;
use syntax::{abi,ast,visit};

#[deriving(Show)]
pub struct Header {
  structs: Vec<Struct>,
  funcs: Vec<Function>
}

#[deriving(Show)]
pub struct Function {
  name: String,
  ret: CType,
  args: Vec<Arg>
}

#[deriving(Show)]
pub struct Arg {
  c_type: CType,
  name: Option<String>
}

#[deriving(Show)]
pub struct Struct {
  path: Vec<String>,        // Struct name and module path
  fields: Option<Vec<Arg>>  // Struct fields (unless opaque)
}

#[deriving(Show)]
pub enum CType {
  CVoid,                  // void
  U8,                     // uint8_t
  U16,                    // uint16_t
  U32,                    // uint32_t
  U64,                    // uint64_t
  UIPtr,                  // uintptr_t
  I8,                     // int8_t
  I16,                    // int16_t
  I32,                    // int32_t
  I64,                    // int64_t
  IPtr,                   // intptr_t
  CStruct(ast::DefId),    // Struct
  CPtr(Box<CType>),       // C pointer
  CArr(Box<CType>, uint)  // Fixed length array
}

struct Generator {
  funcs: Vec<Function>,
  tcx: ty::ctxt
}

pub fn gen(file: &Path, libs: &[Path]) -> Result<Header, ()> {
  let input = driver::FileInput(file.clone());
  let session = build_rustc_session(file, libs);
  let config = config::build_configuration(&session);

  // Run the compiler
  let krate = driver::phase_1_parse_input(&session, config, &input);
  let (krate, ast) = driver::phase_2_configure_and_expand(&session, &mut Loader::new(&session), krate, &crate_id("foo"));
  let analysis = driver::phase_3_run_analysis_passes(session, &krate, ast);

  // Setup the visitor
  let mut gen = Generator::new(analysis.ty_cx);

  // Crawl the crate and gather the C ABI func definitions
  visit::walk_crate(&mut gen, &krate, ());

  // Get all structs
  let structs = gen.get_structs();

  Ok(Header {
    structs: structs,
    funcs: gen.funcs
  })
}

impl Struct {
  fn is_passed_by_value(&self) -> bool {
    self.fields.is_some()
  }
}

impl Generator {
  fn new(tcx: ty::ctxt) -> Generator {
    Generator {
      funcs: Vec::new(),
      tcx: tcx
    }
  }

  fn get_structs(&self) -> Vec<Struct> {
    let mut lookup = HashMap::new();

    for func in self.funcs.iter() {
      self.load_struct_into(&mut lookup, &func.ret, true);
    }

    lookup.move_iter().map(|(_,s)| s).collect()
  }

  fn load_struct_into(&self, into: &mut HashMap<ast::DefId, Struct>, c_type: &CType, by_val: bool) {
    match c_type {
      &CPtr(ref nested) => self.load_struct_into(into, *nested, false),
      &CStruct(def_id) => {
        if !into.contains_key(&def_id) || (by_val && !into.get(&def_id).is_passed_by_value()) {
          into.insert(def_id, self.def_id_to_struct(def_id, by_val));
        }
      },
      &CArr(..) => unimplemented!(),
      _ => return
    }
  }

  fn arg_from_t(&self, name: Option<String>, ty: ty::t) -> Arg {
    Arg {
      name: name,
      c_type: self.c_type_from_t(ty)
    }
  }

  fn ty_to_t(&self, ty: &ast::Ty) -> ty::t {
     astconv::ast_ty_to_ty(self, &infer::new_infer_ctxt(&self.tcx), ty)
  }

  fn c_type_from_ty(&self, ty: &ast::Ty) -> CType {
    let t = astconv::ast_ty_to_ty(self, &infer::new_infer_ctxt(&self.tcx), ty);
    self.c_type_from_t(t)
  }

  fn c_type_from_t(&self, t: ty::t) -> CType {
    match ty::get(t).sty {
      ty::ty_nil |
      ty::ty_bot => CVoid,
      ty::ty_bool => fail!("bool is not FFI compatible"),
      ty::ty_char => U32,

      ty::ty_int(i) => {
        match i {
          ast::TyI8 => I8,
          ast::TyI16 => I16,
          ast::TyI32 => I32,
          ast::TyI64 => I64,
          ast::TyI => IPtr
        }
      }

      ty::ty_uint(i) => {
        match i {
          ast::TyU8 => U8,
          ast::TyU16 => U16,
          ast::TyU32 => U32,
          ast::TyU64 => U64,
          ast::TyU => UIPtr
        }
      }

      ty::ty_float(_) => {
        fail!("float support not implemented")
      }

      ty::ty_box(t) |
      ty::ty_ptr(ty::mt { ty: t, .. }) |
      ty::ty_rptr(_, ty::mt { ty: t, .. }) |
      ty::ty_uniq(t) => {
        match ty::get(t).sty {
          ty::ty_str => fail!("&str (and company) are not exposed. Use a custom struct instead."),
          _ => CPtr(box self.c_type_from_t(t))
        }
      }

      ty::ty_enum(def_id, _) => {
        match magic_ctype(self.full_name(def_id).as_slice()) {
          Some(t) => t,
          None => fail!("enum types are not FFI compatible")
        }
      }

      ty::ty_struct(def_id, _) => {
        match magic_ctype(self.full_name(def_id).as_slice()) {
          Some(t) => t,
          None => CStruct(def_id)
        }
      }

      // Unsupported
      ty::ty_str => fail!("unsupported type &str"),
      ty::ty_vec(..) => fail!("unsupported type &[T]"),
      ty::ty_bare_fn(..) => fail!("unsupported type ty_bare_fn"),
      ty::ty_closure(..) => fail!("unsupported type ty_closure"),
      ty::ty_trait(..) => fail!("unsupported type ty_trait"),
      ty::ty_tup(..) => fail!("unsupported type ty_tup"),
      ty::ty_param(..) => fail!("unsupported type ty_param"),
      ty::ty_self(..) => fail!("unsupported type ty_self"),
      ty::ty_infer(..) => fail!("unsupported type ty_infer"),
      ty::ty_err(..) => fail!("unsupported type ty_err")
    }
  }

  fn def_id_to_struct(&self, def_id: ast::DefId, by_value: bool) -> Struct {
    let ty = ty::lookup_item_type(&self.tcx, def_id);

    let fields = match ty::get(ty.ty).sty {
      ty::ty_struct(_, ref info) => {
        if by_value {
          let mut fields = Vec::new();

          for field in ty::struct_fields(&self.tcx, def_id, info).iter() {
            let name = String::from_str(token::get_ident(field.ident).get());
            fields.push(self.arg_from_t(Some(name), field.mt.ty));
          }

          Some(fields)
        }
        else {
          None
        }
      }
      _ => fail!("something went wrong")
    };

    Struct {
      path: self.full_name(def_id),
      fields: fields
    }
  }

  fn full_name(&self, def_id: ast::DefId) -> Vec<String> {
    ty::with_path(&self.tcx, def_id, |elems| {
      elems.map(|e| token::get_name(e.name()).get().to_string()).collect()
    })
  }
}

impl visit::Visitor<()> for Generator {
  fn visit_fn(&mut self, kind: &visit::FnKind, decl: &ast::FnDecl, block: &ast::Block, span: Span, _: ast::NodeId, _: ()) {
    match *kind {
      visit::FkItemFn(name, _, _, abi::C) => {
        let name = token::get_ident(name);
        let ret = self.c_type_from_ty(decl.output);
        let mut args = Vec::new();

        for arg in decl.inputs.iter() {
          let t = self.ty_to_t(arg.ty);
          args.push(self.arg_from_t(arg_name(arg), t));
        }

        self.funcs.push(Function {
          name: String::from_str(name.get()),
          ret: ret,
          args: args
        });
      }
      _ => {}
    }

    // Continue to traverse
    visit::walk_fn(self, kind, decl, block, span, ());
  }
}

impl astconv::AstConv for Generator {
  fn tcx<'a>(&'a self) -> &'a ty::ctxt {
    &self.tcx
  }

  fn get_item_ty(&self, id: ast::DefId) -> ty::ty_param_bounds_and_ty {
    ty::lookup_item_type(&self.tcx, id)
  }

  fn get_trait_def(&self, id: ast::DefId) -> Rc<ty::TraitDef> {
    ty::lookup_trait_def(&self.tcx, id)
  }

  fn ty_infer(&self, _: Span) -> ty::t {
    infer::new_infer_ctxt(&self.tcx).next_ty_var()
  }
}

fn arg_name(arg: &ast::Arg) -> Option<String> {
  match arg.pat.node {
    ast::PatIdent(_, ref path, _) => {
      Some(token::get_ident(path.segments.get(0).identifier).get().to_string())
    }
    _ => None
  }
}

fn build_rustc_session(file: &Path, libs: &[Path]) -> session::Session {
  session::build_session(session_opts(libs), Some(file.clone()))
}

fn session_opts(libs: &[Path]) -> config::Options {
  let paths: HashSet<Path> = libs.iter().map(|p| p.clone()).collect();

  config::Options {
    maybe_sysroot: detect_sysroot(),
    addl_lib_search_paths: RefCell::new(paths),
    crate_types: vec!(config::CrateTypeRlib),
    lint_opts: vec!((lint::Warnings, lint::Allow)),
    ..config::basic_options().clone()
  }
}

fn detect_sysroot() -> Option<Path> {
  let out = match Command::new("which").arg("rustc").output() {
    Ok(o) => o,
    Err(_) => return None
  };

  Some(Path::new(out.output.as_slice()).dir_path().dir_path())
}

fn crate_id(name: &str) -> CrateId {
  from_str(name).unwrap()
}

fn magic_ctype(path: &[String]) -> Option<CType> {
  if path.is_empty() {
    return None;
  }

  if path[0].as_slice() == "libc" {
    let last = path.last().map(|s| s.as_slice());

    if last == Some("c_void") {
      return Some(CVoid)
    }
  }

  None
}

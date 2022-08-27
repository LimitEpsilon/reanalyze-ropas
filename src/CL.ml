(* Compiler libs: use the host compiler libs except on 4.06 use vendored ones.
   This allows to target 4.06 on any compiler by overriding OCAML_VERSION. *)
[%%import "../config.h"]
[%%if ocaml_version <= (4, 06, 1) || defined npm]

include Compilerlibs406

[%%else]

module Asttypes = Asttypes
module Btype = Btype
module Cmt_format = Cmt_format
module Ident = Ident
module Env = Env
module Location = Location
module Longident = Longident
module Misc = Misc
module Parsetree = Parsetree
module Path = Path
module Primitive = Primitive
module Printpat = Printpat
module Tast_mapper = Tast_mapper
module Typedtree = Typedtree
module Types = Types

[%%endif]

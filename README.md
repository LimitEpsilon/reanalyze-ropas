# reanalyze-ropas

This repository utilizes the frontend developed in [reanalyze](https://github.com/rescript-association/reanalyze), and attempts to improve upon the exception analysis feature that reanalyze provides. The dead-code elimination and termination analysis features are not implemented and are kept in their original forms. For improved dead code analysis, refer to [Jhuni0123/redder](https://github.com/Jhuni0123/redder), which also improves upon the worklist algorithm used in this codebase. The code of the original reanalyze repository and the code for exa are licensed under the MIT [license](LICENSE).

## Exception Analysis
The newly implemented exception analysis follows the approach taken in [Ryu and Yi, Towards a Cost-Effective Estimation of Uncaught Exceptions in SML Programs](https://dl.acm.org/doi/10.5555/647166.717966). Support for references and mutable record fields and experimental support for accurate pattern filtering is added as to cover realistic programs, but the hacky implementation in this development makes the analysis unsound.
An informal documentation in pdf form can be found [here](TeX/main.pdf).

Running the analysis prints out what exceptions can be raised from the toplevel of each file, and prints out what the arguments of each exception might contain.

### Build for Native Projects

```shell
dune build
./_build/default/src/Reanalyze.exe -exception-cmt <path-to-cmt-files>
```
An example that analyzes possible exceptions in the standard library of OCaml is:

```shell
cd ~/.opam/<ocaml-version>/lib/ocaml
<path to binary> -exclude-paths "./compiler-libs,./ocamldoc,./topdirs" -exception-cmt .
```
To track where the exception originates from, add the flag `-exception-track <exception constructor>` before `-exception-cmt`.

### Build for ReScript

```shell
npm run build406
./_build/default/src/Reanalyze.exe -exception-cmt <path-to-cmt-files>
```

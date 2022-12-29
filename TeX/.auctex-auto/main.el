(TeX-add-style-hook
 "main"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "a4paper")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("unicode-math" "math-style=TeX" "bold-style=TeX")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "graphicx"
    "kotex"
    "tabularray"
    "listings"
    "amssymb"
    "amsmath"
    "mathtools"
    "unicode-math"
    "newunicodechar"
    "ebproof"
    "simplebnf")
   (TeX-add-symbols
    '("loverbar" 1)
    "textfallback"
    "vbar"
    "finto"
    "istype"
    "ortype"
    "Reanalyze"
    "Memory"
    "Loc"
    "Value"
    "Env"
    "Id"
    "Closure"
    "Const"
    "Exn"
    "Arr"
    "Lbl"
    "List"
    "Expr"
    "Ctor"
    "Packet"
    "Prim"
    "Op")
   (LaTeX-add-xparse-macros
    '("\\RenewDocumentCommand\\SimpleBNFDefEq{}" "SimpleBNFDefEq" "" "Renew")))
 :latex)


## Exception analysis

The exception analysis is designed to keep track statically of the exceptions that might be raised at runtime. It works by issuing warnings and recognizing annotations. Warnings are issued whenever an exception is raised and not immediately caught. Annotations are used to push warnings from he local point where the exception is raised, to the outside context: callers of the current function.
Nested functions need to be annotated separately.

Instructions on how to run the exception analysis using the `-exception` and `-exception-cmt` command-line arguments, or how to add `"analysis": ["exception"]` in `bsconfig.json` are contained in the general [README.md](README.md).

Here's an example, where the analysis reports a warning any time an exception is raised, and not caught:

```rescript
let raises = () => raise(Not_found)
```

reports:

```sh

  Exception Analysis
  File "A.res", line 1, characters 4-10
  raises might raise Not_found (A.res:1:19) and is not annotated with @raises(Not_found)
```

No warning is reporteed when a `@raises` annotation is added:

```rescript
@raises(Not_found)
let raises = () => raise(Not_found)
```

When a function raises multiple exceptions, a tuple annotation is used:


```rescript
exception A
exception B

@raises([A, B])
let twoExceptions = (x, y) => {
  if (x) {
    raise(A)
  }
  if (y) {
    raise(B)
  }
}
```

It is possible to silence the analysis by adding a `@doesNotRaise` annotaion:

```rescript
@raises(Invalid_argument)
let stringMake1 = String.make(12, ' ')

// Silence only the make function
let stringMake2 = (@doesNotRaise String.make)(12, ' ')

// Silence the entire call (including arguments to make)
let stringMake3 = @doesNotRaise String.make(12, ' ')

```

## Limitations

- The libraries currently modeled are limited to `Array`, `Buffer`, `Bytes`, `Char`, `Filename`, `Hashtbl`, `List`, `Pervasives`, `Str`, `String` from the standard library, and `bs-json`, and `Json` from `Js`. Models are currently vendored in the analysis, and are easy to add (see [`src/ExnLib.ml`](src/ExnLib.ml))
- Generic exceptions are not understood by the analysis. For example `exn` is not recognized below (only concrete exceptions are):

```rescript
try (foo()) { | exn => raise(exn) }
```

- Uses of e.g. `List.hd` are interpered as belonging to the standard libry. If you re-define `List` in the local scope, the analysis it will think it's dealing with `List` from the standard library.

- There is no special support for functors. So with `Hashtbl.Make(...)` the builtin model will not apply. So the analysis won't report that the following can raise `Not_found`:

```rescript
module StringHash =
  Hashtbl.Make({
    include String
    let hash = Hashtbl.hash
  })
let specializedHash = tbl => StringHash.find(tbl, "abc")
```

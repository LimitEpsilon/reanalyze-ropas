Dependency graph:
```
   SetExpression
    ↑         ↑
    |         |
Exception → Reduce
```

`Exception` includes the following pipeline:
1. `SetExpression` generates set constraints,
2. `Exception` resolves path (identify possibly ambiguous identifiers using `Path.t`),
3. and `Reduce` reduce the set constraints.

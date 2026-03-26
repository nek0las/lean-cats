# lean-cats

`lean-cats` is a Lean 4 project for experimenting with weak memory models and litmus tests.
It supports:

- A CAT-style DSL in Lean (`[model| ... ]`) for defining models.
- Candidate executions (`CandidateExecution`) and core relations (`po`, `rf`, `co`, `fr`).
- Litmus parsing/enumeration plus reader commands (`#litmus`, `deflitmus`).
- Model loading from `.cat` / `.bell` files (`defcat <"...">`).

## Usage

### Building

```bash
git clone <repo-url>
cd lean-cat
lake update
lake build
```

### Running the included tools

```bash
lake exe litmus-parser-test
```

### Typechecking a file

```bash
lake env lean LeanCats/Linux/litmus.lean
```

### Using the reader commands

```lean
#litmus "LeanCats/Cats/examples/tests/SB.litmus"
deflitmus SB <"LeanCats/Cats/examples/tests/SB.litmus">

defcat <"sc.cat">
defcat <"tso.cat">
```

## Where to look

- `LeanCats/Macro.lean`: CAT DSL (`[model| ... ]`).
- `LeanCats/Basic.lean`: `CandidateExecution`.
- `LeanCats/LitmusParser/*`: litmus parser/enumerator.
- `LeanCats/LitmusReader.lean` and `LeanCats/ModelReader.lean`: `#litmus` / `deflitmus` / `defcat`.

## References

- Herding Cats (CAT): <https://arxiv.org/pdf/1308.6810>
- herdtools7 ecosystem: <https://github.com/herd/herdtools7>
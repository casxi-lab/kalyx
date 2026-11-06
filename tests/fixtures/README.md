# Test fixtures

`integer_paths.tsv` holds 518 exact answers for the integer and mixed paths
of rational arithmetic at word boundaries of 31 to 1024 bits. The test
`integer_and_mixed_paths_match_independent_exact_answers` in
`tests/numbers.rs` evaluates every row through the number API and compares
both parts of the result; the rows were taken over from the earlier
implementation without running any of its code (see [Sources](#sources)).

## Format

The file is plain TSV: UTF-8 text with tab-separated columns, no comment
lines and no empty lines, so that any TSV reader, including the file view on
GitHub, takes the first line as the header. The first line is the header row,
which names the four columns in order:

```text
id	source	numerator	denominator
```

Every following line is one row with these four columns:

| Column | Meaning |
| --- | --- |
| `id` | A unique name of the row. |
| `source` | An expression over decimal literals, which may have leading zeros and a fraction part, with `+`, `-`, `*`, `/`, `^` with an integer exponent, unary `-` and parentheses, and no spaces. |
| `numerator` | The numerator of the exact value of `source` in lowest terms, in decimal, with a leading `-` when negative. |
| `denominator` | The positive denominator of that value, in decimal. |

`tests/numbers.rs` rejects a file whose first line is not the header row,
any comment or empty line after it, a row without exactly four columns and a
repeated `id`.

## Sources

The 518 rows of `integer_paths.tsv` come from
`cas-project@f2d2fba26cbf09474e6df8e59650014ae58dec78:fixtures/integer_paths.tsv`,
a fixture of the earlier implementation, unchanged and in their order there;
only its comment lines were replaced by the header row. The expected values
were computed by an independent generator with exact integer and rational
arithmetic; the generator is not public.

# Polynomial coefficients from roots in ACL2: rump-session development

Books for the ACL2 2026 Workshop rump session (#19, "Pencil, Chalkboard, Q.E.D.").
They extend the book `poly-roots-coeffs.lisp` of the Spanish-language CVM 2026
papers by P. O. Cayuela, which stays untouched, as published, in
[acl2-poly-roots-coeffs](https://github.com/pcayuela/acl2-poly-roots-coeffs)
(branch `main`). Nothing here changes that repository.

## Branches (each one contains all the previous ones)

| Branch | Adds | Flavours |
|--------|------|----------|
| `rumpsession` | guards, `cardano-vieta`, nested sums and chains, permutations, ACL2(r) examples | ACL2, ACL2(r) |
| `newton-girard` | `poly-roots-newton-girard`: Newton-Girard identities, power sums | ACL2, ACL2(r) |
| `traces-v4` | `poly-roots-traces` on Russinoff's `projects/linear` (frozen, as in slides v4) | ACL2 only |
| `traces` | `poly-roots-traces`, self-contained: determinant by cofactors, characteristic polynomial of an upper-triangular matrix from the traces of its powers | ACL2, ACL2(r) |
| `leibniz` / `main` | `poly-roots-leibniz`: the cofactor determinant equals Leibniz's formula (sum over permutations) | ACL2 only |

`main` is `leibniz` plus this README. Each branch certifies from a clean clone
in ACL2 8.7 and ACL2(r) 8.7(r) (Docker image `ghcr.io/pcayuela/acl2-acl2r-docker:8.7`),
except where the table says ACL2 only. Certify with `cert.pl <book>` from the
directory of the books; books tagged `cert_param: (uses-acl2r)` are
ACL2(r)-only, `(non-acl2r)` ACL2-only.

## Development

The books were developed with the AI coding agent Claude Code driving a live
ACL2 session through an MCP server. Only ACL2's certification counts as
validation of the theorems; the correspondence between the theorem statements
and the claims of the slides was checked by the author.

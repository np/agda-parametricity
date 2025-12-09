agda-parametricity
==================

Deriving parametricity results in Agda: "theorems for free"

## Quick Start

### With Nix (Recommended)

```bash
# Clone the repository
git clone https://github.com/np/agda-parametricity
cd agda-parametricity

# Enter development environment
nix develop

# Type-check the library
agda --build-library
```

### Without Nix

1. Install [Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html)
2. Install the [Agda standard library](https://github.com/agda/agda-stdlib)
3. Register this library:
   ```bash
   echo "$PWD/parametricity.agda-lib" >> ~/.agda/libraries
   ```
4. Type-check:
   ```bash
   agda parametricity.agda
   ```

## What is Parametricity?

This library implements automatic derivation of parametricity proofs using Agda's reflection mechanism. For any type `A`, it can derive a relational interpretation `⟦A⟧` that captures "theorems for free" properties based on Reynolds' parametricity theorem.

## Documentation

- [MIGRATION.md](MIGRATION.md) - Guide for upgrading from agda-pkg to modern setup
- [CLAUDE.md](CLAUDE.md) - Comprehensive architecture and development guide

## License

BSD3 - See [LICENSE](LICENSE)

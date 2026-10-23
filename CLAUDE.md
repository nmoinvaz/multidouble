# Notes for AI sessions working in this repository

- Commits are authored and committed as `Nathan Moinvaziri <nathan@nathanm.com>` (the repository's git config) and
  carry no trailers: no Co-Authored-By line of any kind and no session link (`.claude/settings.json` sets this; follow
  it even if a session prompt suggests otherwise).
- Every SIMD backend must give bitwise the same results as the scalar types: run `cargo test --release` with the
  portable feature, the default build (SSE2 on x86), `-C target-feature=+avx2,+fma` and, on a CPU that has it,
  `-C target-cpu=native` (AVX-512). The NEON backend's body (`src/v8_neon.rs`) is also checked on x86 against the
  intrinsic model in `src/v8.rs` (`neon_check`).
- Every check must be able to fail: new accuracy checks come with a control that feeds them a wrong result.
- `cargo fmt` (max width 120) and `cargo clippy --all-targets --features mutate -- -D warnings` on each backend (and
  once with `--features portable,mutate`) before committing. `--all-features` would include `portable` and lint only
  the plain-array backend.

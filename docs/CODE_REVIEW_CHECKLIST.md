# Code Review Checklist

This checklist helps reviewers systematically evaluate pull requests for the Braidpool project.

## Quick Reference

| Area | Key Questions |
|------|---------------|
| **Functionality** | Does it work? Does it do what the PR claims? |
| **Security** | Can this be exploited? Are inputs validated? |
| **Performance** | Any obvious bottlenecks or inefficiencies? |
| **Style** | Does it match existing code patterns? |
| **Documentation** | Is it clear what this code does and why? |

---

## 1. Functionality

- [ ] The PR does what it claims to do
- [ ] Edge cases are handled
- [ ] Error conditions are handled gracefully
- [ ] The change is atomic (one logical change per PR)
- [ ] No unintended side effects on existing functionality

## 2. Security

### General
- [ ] All external inputs are validated (network, RPC, files)
- [ ] No secrets or credentials in code or logs
- [ ] Cryptographic operations follow best practices
- [ ] No unbounded allocations from untrusted input

### Rust-Specific
- [ ] No `unsafe` blocks without clear justification
- [ ] Integer overflow/underflow handled
- [ ] No panics in production paths (`unwrap()`, `expect()`, array indexing)

### TypeScript-Specific
- [ ] User input is sanitized before display (XSS prevention)
- [ ] API responses are validated before use
- [ ] No sensitive data in browser storage or logs

## 3. Performance

- [ ] No obvious O(n²) or worse algorithms on large data
- [ ] Allocations minimized in hot paths
- [ ] No blocking calls in async context
- [ ] Database/network calls batched where possible
- [ ] No memory leaks (especially in long-running processes)

## 4. Code Style

### Rust
- [ ] Passes `cargo fmt`
- [ ] Passes `cargo clippy` without warnings
- [ ] Idiomatic Rust (proper use of `?`, iterators, etc.)
- [ ] Error types are appropriate and informative

### TypeScript
- [ ] Passes `npx prettier --check .`
- [ ] No `any` types
- [ ] React hooks follow rules
- [ ] Consistent naming conventions

## 5. Testing

- [ ] Tests exist for new functionality
- [ ] Tests cover both happy path and error cases
- [ ] Tests are deterministic (no flaky tests)
- [ ] Test names clearly describe what they test
- [ ] Mocks are used appropriately

## 6. Documentation

- [ ] Public APIs have documentation comments
- [ ] Complex logic has explanatory comments
- [ ] README updated if user-facing behavior changes
- [ ] Breaking changes documented

## 7. Architecture

- [ ] Fits existing project structure
- [ ] No unnecessary dependencies added
- [ ] Separation of concerns maintained
- [ ] No circular dependencies introduced

---

## Severity Levels for Findings

| Level | Icon | Description | Action |
|-------|------|-------------|--------|
| Critical | 🔴 | Security vulnerability, data loss, consensus bug | Must fix before merge |
| High | 🟠 | Bugs, panics in production, spec violations | Should fix before merge |
| Medium | 🟡 | Performance issues, non-idiomatic code | Consider fixing |
| Low | 🟢 | Style suggestions, minor improvements | Optional |

---

## Review Comment Best Practices

1. **Be specific**: Point to exact lines, suggest exact fixes
2. **Be constructive**: Explain *why* something is an issue
3. **Prioritize**: Use severity labels so authors know what matters
4. **Ask questions**: If unsure, ask rather than assume
5. **Acknowledge good work**: Positive feedback is valuable too

## Example Review Comment

```markdown
🟠 **High**: This `unwrap()` on line 42 will panic if the peer sends malformed data.

**Suggestion:**
```rust
// Before
let value = response.parse().unwrap();

// After
let value = response.parse().map_err(|e| {
    error!("Failed to parse response: {}", e);
    ProtocolError::MalformedResponse
})?;
```
```

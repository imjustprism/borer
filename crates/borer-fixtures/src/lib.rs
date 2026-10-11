//! Programs compiled as test fixtures for borer's engine tests.
//!
//! The fixtures are this package's examples. They live apart from the
//! engine so the workspace profile can build them unoptimized while
//! everything else builds optimized: a fixture's compiled shape is what the
//! test checks, and optimization changes it.

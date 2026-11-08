//! The upstream ShellCheck pin in `tools/oracle.json`, copied to this crate's
//! `upstream.json` so the published package builds without the repository.

use serde::Deserialize;

/// The upstream ShellCheck source the port follows and the oracle builds from.
#[derive(Deserialize, Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "schema", derive(schemars::JsonSchema))]
pub struct UpstreamPin {
    /// The GitHub repository, as `owner/name`.
    pub repository: String,
    /// The full commit SHA of the pinned source.
    pub revision: String,
    /// The version that `ShellCheck.cabal` declares at that revision.
    pub version: String,
}

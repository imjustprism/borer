# Turning on the package managers

The release workflow (`.github/workflows/release.yml`) builds every package
from the GitHub release's archives (`scripts/dev/packages.py`) and publishes
it after the release job, but each publish job is skipped until its
credential exists. Nothing here is set up yet. Do the steps in order; each
ends with one command that shows it worked. GitHub secrets and variables go
under the borer repository's Settings > Secrets and variables > Actions.

All names below are free as of 2026-10-28 (`borer` is taken on npm, hence
`borer-mcp`).

## 1. crates.io: `cargo install borer`, `cargo binstall borer`

1. Sign in at https://crates.io with the GitHub account `imjustprism` and
   verify an email address (crates.io refuses to publish without one).
2. Account Settings > API Tokens > New Token: name `borer release`, scopes
   `publish-new` and `publish-update`, crate pattern `borer*` (it covers
   `borer`, `borer-engine` and `borer-live`).
3. Add it as the secret `CARGO_REGISTRY_TOKEN`.

The next tag publishes `borer-engine`, `borer-live` and `borer`, in that
order. The three names then belong to the account; a rerun of a published
version fails that job (crates.io refuses a version twice) and nothing else.

Verify: `cargo binstall borer --no-confirm` (it takes the release archive
named in `[package.metadata.binstall]` of `crates/borer/Cargo.toml`).

## 2. npm: `npm install -g borer-mcp`, `npx -y borer-mcp`

1. Create an account at https://www.npmjs.com and turn on two-factor
   authentication.
2. Access Tokens > Generate New Token > Granular Access Token: name
   `borer release`, Packages and scopes: Read and write, All packages (the
   five names do not exist yet, so they cannot be picked one by one), and
   allow it to bypass two-factor authentication for publishing. Note its
   expiry date: npm limits how long a write token lives, and an expired one
   fails the npm job until it is replaced.
3. Add it as the secret `NPM_TOKEN`.

The next tag publishes `borer-mcp-win32-x64`, `borer-mcp-linux-x64`,
`borer-mcp-darwin-x64`, `borer-mcp-darwin-arm64` and then `borer-mcp`, each
with provenance. After the first publish, the token can be narrowed to those
five packages, or replaced by npm trusted publishing (each package's
Settings > Trusted Publisher: GitHub Actions, `imjustprism/borer`,
workflow `release.yml`), which needs no secret but a change to the npm job.

Verify: `npx -y borer-mcp --version`

## 3. PyPI: `pipx install borer`, `uvx borer`

PyPI publishing uses trusted publishing, so there is no token to store.

1. Create an account at https://pypi.org and turn on two-factor
   authentication.
2. Account > Publishing > Add a new pending publisher > GitHub: PyPI
   project name `borer`, owner `imjustprism`, repository `borer`, workflow
   name `release.yml`, environment name `pypi`.
3. Add the repository variable (Variables tab, not Secrets) `PYPI_PUBLISH`
   with the value `true`. The `pypi` environment is created by the first
   run; it needs no settings.

The next tag uploads the four wheels (Windows x64, manylinux x86_64, macOS
x86_64 and arm64); a rerun skips the files PyPI already has.

Verify: `uvx borer --version`

## 4. Homebrew: `brew install imjustprism/tap/borer`

1. Create the public repository `imjustprism/homebrew-tap` with a README
   (so it has a default branch). Copy `packaging/homebrew/borer.rb` to
   `Formula/borer.rb` in it and push: that makes v0.2.5 installable at once.
2. Create a fine-grained personal access token (GitHub Settings > Developer
   settings > Fine-grained tokens): name `borer tap`, resource owner
   `imjustprism`, only the repository `imjustprism/homebrew-tap`,
   permission Contents: Read and write. It expires; renew it before then.
3. Add it as the secret `HOMEBREW_TAP_TOKEN`.

Each tag then commits the new `Formula/borer.rb` to the tap.

Verify: `brew install imjustprism/tap/borer && brew test borer`

## 5. Scoop: `scoop install imjustprism/borer`

1. Create the public repository `imjustprism/scoop-bucket` with a README.
   Copy `packaging/scoop/borer.json` to `bucket/borer.json` in it and push.
2. Create a fine-grained personal access token as in step 4, for the
   repository `imjustprism/scoop-bucket` only, Contents: Read and write.
3. Add it as the secret `SCOOP_BUCKET_TOKEN`.

Each tag then commits the new `bucket/borer.json`. The manifest also carries
`checkver` and `autoupdate`, so Scoop's own updater (Excavator) can bump it
from GitHub releases if the token ever lapses.

Verify:

```powershell
scoop bucket add imjustprism https://github.com/imjustprism/scoop-bucket
scoop install imjustprism/borer; borer --version
```

## Afterwards

- The next `v*` tag runs everything; the `registries` job of that run lists
  which publishers were on (`crates=true` and so on). A job left off shows
  as skipped and the release stays green.
- To try a package before a tag:
  `gh release download v0.2.5 -R imjustprism/borer -D dist`, then
  `python scripts/dev/packages.py npm dist out` (or `wheels dist out`,
  `manifests dist`).
- When all five are live, update the Install section of README.md: it marks
  these commands as not published yet.

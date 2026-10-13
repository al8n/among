# Release checklist

Use this checklist to keep the crate version, release commit, tag, GitHub release, and crates.io release aligned.

1. Set the final version in `Cargo.toml`, update the README examples, and finalize `CHANGELOG.md`.
2. Run the repository's release validation suite, including package and SemVer compatibility checks.
3. Commit the validated release preparation with the exact version in the commit message.
4. Create and push the matching `v<version>` tag from that release commit.
5. Create the GitHub release from the same tag and use the matching changelog notes.
6. Publish that exact tagged source to crates.io, then verify the published version and docs.

This preparation task does not publish a crate, create a tag, push changes, or create a GitHub release.

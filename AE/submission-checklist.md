# CAV 2026 Artifact Submission Checklist

Reference: [CAV 2026 Artifact Evaluation](https://conferences.i-cav.org/2026/artifacts/)

## Required Form Fields

- [ ] Paper ID and title
- [ ] Paper abstract
- [ ] Accepted paper PDF
- [ ] Artifact download URL (`.zip`)
- [ ] Confirm URL access is not author-trackable
- [ ] SHA256 checksum of the `.zip`
- [ ] Artifact type: Docker image
- [ ] Architecture: `x86_64`
- [ ] External connectivity declaration
- [ ] Requested badges: Available + Reusable

## Package Content Check

- [ ] `image.tar.gz` included
- [ ] `README.md` included
- [ ] `LICENSE` included
- [ ] Smoke/full review commands are documented in `README.md`

## Badge-Oriented Checks

### Available
- [ ] DOI points to exact submitted version (not concept DOI)
- [ ] License permits running/examining artifact inside and outside AE

### Reusable
- [ ] Dependencies documented and reproducible
- [ ] README includes usage beyond paper replication
- [ ] Extension points/documented interfaces described
- [ ] Optional non-Docker setup path documented

## Final Sanity

- [ ] Test from a clean machine/container only using README
- [ ] Smoke-test works end-to-end
- [ ] Full-review runs and produces expected outputs
- [ ] ZIP and SHA256 regenerated after final edits

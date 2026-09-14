# Audited public inputs

`fetch-public-cases.sh` obtains the two unmodified repositories and detached
commits assessed by the S3 public-case audit.  It refuses a pre-existing
destination and checks the metamodel, one Train snapshot and the EMF Compare
metamodel hashes.  It does not run a benchmark, import XMI or claim an EMF
Compare result.

The audit, input inventory, mapping classification and expected bridge
observations are in the external worker report:
`/home/xoruser/msc-5/misc/third_review/development/reports/s3/README.md`.

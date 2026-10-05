# Requests from lane C to lane A

## 2. Remove the module PaperMainSymmetricDiagonalizationEigen

No module requires `theories/PaperMainSymmetricDiagonalizationEigen.v` any
more: `PaperMainSymmetricDiagonalization` now takes the spectral theorem from
`library/matrix/real_spectral.v`. Please delete the file and its line in
`_CoqProject`.

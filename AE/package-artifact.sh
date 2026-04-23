#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
IMAGE_NAME="autoq-cav26"
SOURCE_README="${SCRIPT_DIR}/README.md"
ZIP_NAME="autoq-cav26-artifact.zip"
PKG_DIR="${SCRIPT_DIR}/artifact-package"
PKG_IMAGE="${PKG_DIR}/image.tar.gz"

if [[ ! -f "${SOURCE_README}" ]]; then
  echo "[AE] Missing README source: ${SOURCE_README}" >&2
  exit 1
fi

cd "${REPO_ROOT}"
echo "[AE] Building Docker image ${IMAGE_NAME} for linux/amd64"
docker build --platform=linux/amd64 -f "${SCRIPT_DIR}/Dockerfile.ae" -t "${IMAGE_NAME}" .
echo "[AE] Docker image ready: ${IMAGE_NAME}"

cd "${SCRIPT_DIR}"
mkdir -p "${PKG_DIR}"

echo "[AE] Exporting Docker image ${IMAGE_NAME}"
docker save "${IMAGE_NAME}" | gzip > "${PKG_IMAGE}"

cp "${SOURCE_README}" "${PKG_DIR}/README.md"
cp "${REPO_ROOT}/LICENSE" "${PKG_DIR}/LICENSE"

(
  cd "${PKG_DIR}"
  zip -r "../${ZIP_NAME}" .
)

sha256sum "${SCRIPT_DIR}/${ZIP_NAME}" | tee "${SCRIPT_DIR}/${ZIP_NAME}.sha256"

echo "[AE] Package complete:"
echo "  - ${SCRIPT_DIR}/${ZIP_NAME}"
echo "  - ${SCRIPT_DIR}/${ZIP_NAME}.sha256"

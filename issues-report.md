# AutoQ `run` 分支問題檢查報告

> 檢查日期：2026-03-13
> 分支：`run`（最新 commit: `a087eff73`）
> 目標：為 TACAS'25 論文建立 artifact evaluation 支援（`run.sh`、Docker、RUS benchmark 腳本）

---

## 嚴重問題（會導致功能無法運作）

### 1. Dockerfile 基礎映像名稱錯誤

| 項目 | 內容 |
|------|------|
| 檔案 | `Dockerfile:1` |
| 現況 | `FROM --platform=linux/amd64 ubuntu:22.04-slim` |
| 問題 | Ubuntu 官方 Docker Hub 沒有 `-slim` 變體。Ubuntu 映像 tag 只有 `ubuntu:22.04`、`ubuntu:jammy` 等。`-slim` 是 Debian 系列的慣例（如 `debian:bookworm-slim`），不適用於 Ubuntu。 |
| 影響 | `docker build` 直接失敗，無法拉取基礎映像。 |
| 修正 | 改為 `FROM --platform=linux/amd64 ubuntu:22.04` |

---

### 2. `install-dependencies.sh` 末尾無條件 `exit 1`

| 項目 | 內容 |
|------|------|
| 檔案 | `install-dependencies.sh:69` |
| 現況 | 腳本最後一行為 `exit 1`，無任何條件判斷。 |
| 問題 | 不管前面的安裝步驟是否成功，腳本一律回傳失敗狀態碼。任何依賴此腳本回傳值的 CI/CD 或 Dockerfile `RUN` 指令都會判定為失敗。 |
| 影響 | 使用者按照 README 執行 `./install-dependencies.sh` 會看到失敗訊息；若 Dockerfile 改用此腳本，build 也會中斷。 |
| 修正 | 移除第 69 行的 `exit 1`，或改為 `exit 0`。 |

---

### 3. `install-dependencies.sh` 的 `apt install` 缺少 `sudo`

| 項目 | 內容 |
|------|------|
| 檔案 | `install-dependencies.sh:19-27` |
| 現況 | 直接使用 `apt install g++`、`apt install make` 等指令，沒有 `sudo` 前綴，也沒有 `-y` 自動確認。 |
| 問題 | 在非 root 使用者環境下（多數桌面 Linux、WSL2 預設環境），`apt install` 需要 `sudo` 權限。缺少 `-y` 則會在非互動環境中卡住。 |
| 影響 | 非 root 使用者無法透過此腳本安裝依賴。 |
| 修正 | 改為 `sudo apt install -y g++ make cmake ...` 或在腳本開頭檢查權限後統一處理。 |

---

## 中等問題（不會立即阻擋，但會造成困擾）

### 4. 約 83 MB 的二進位靜態/動態庫被 commit 進 git

| 項目 | 內容 |
|------|------|
| 檔案 | `libz3.a`（48 MB）、`libz3.so.4.12`（32 MB）、`libantlr4-runtime-4.13.2.a`（2.8 MB） |
| 問題 | 大型二進位檔不應直接追蹤在 git 中。每次 clone 都會下載這些檔案，即使它們應該透過套件管理器安裝。 |
| 影響 | 倉庫體積膨脹、clone 速度慢、不同平台的二進位不相容。 |
| 修正建議 | 在 `.gitignore` 中加入 `*.a` 和 `*.so*`，然後用 `git rm --cached` 從追蹤中移除。使用者應透過 `install-dependencies.sh` 或系統套件管理器取得這些庫。 |

---

### 5. Dockerfile 依賴安裝可能不完整

| 項目 | 內容 |
|------|------|
| 檔案 | `Dockerfile:9-21` |
| 現況 | 手動列出了 `g++`、`cmake`、`libboost-*-dev` 等套件，但沒有安裝 `libantlr4-runtime-dev` 或 `libz3-dev`。 |
| 問題 | 專案的 `CMakeLists.txt` / `Makefile` 需要連結 z3 和 antlr4 runtime。目前 Docker build 能成功，可能是因為倉庫中有上述 `.a` 檔案被直接連結（靜態連結）。但這不是正規做法。 |
| 影響 | 如果移除倉庫中的二進位檔（如問題 4 建議），Docker build 的 `make` 階段會連結失敗。 |
| 修正建議 | 在 Dockerfile 的 `apt-get install` 中補上 `libantlr4-runtime-dev` 和 `libz3-dev`（或使用 `install-dependencies.sh` 腳本，前提是先修好問題 2、3）。 |

---

### 6. `README_DOCKER.md` 描述與 Dockerfile 實際行為不一致

| 項目 | 內容 |
|------|------|
| 檔案 | `README_DOCKER.md:40-44` |
| 現況 | 文件描述 `run_benchmarks.sh` 會驗證 4 個 benchmark：Grover/02、Grover/04、MCToffoli/04、BVSym/01。 |
| 實際 | Dockerfile 第 35-40 行建立的 `run_benchmarks.sh` 只執行 `Grover/02` 一個 benchmark。 |
| 修正建議 | 二擇一：(a) 更新 Dockerfile 讓 `run_benchmarks.sh` 實際執行文件所列的 4 個 benchmark，或 (b) 更新 `README_DOCKER.md` 使其與實際行為一致。 |

以下是 Dockerfile 中實際建立的腳本內容（僅跑 1 個 benchmark）：

```bash
# Dockerfile:35-40
echo './build/cli/autoq ver benchmarks/all/Grover/02/pre.hsl \
  benchmarks/all/Grover/02/circuit.qasm \
  benchmarks/all/Grover/02/post.hsl 2>&1'
```

而文件宣稱會跑：
1. `benchmarks/all/Grover/02/` — Grover 搜尋電路
2. `benchmarks/all/Grover/04/` — 較大的 Grover 電路
3. `benchmarks/all/MCToffoli/04/` — 多重控制 Toffoli 閘
4. `benchmarks/CAV23/BVSym/01/` — BV 對稱性驗證

---

### 7. Dockerfile 安裝了非必要的 LaTeX 和圖形套件

| 項目 | 內容 |
|------|------|
| 檔案 | `Dockerfile:18-21` |
| 現況 | 安裝了 `texlive-latex-extra`、`texlive-latex-base`、`texlive-latex-recommended`、`libvips-tools`。 |
| 問題 | 這些套件合計約數百 MB，但 artifact evaluation（`run.sh`）只需要執行 `autoq ver` 指令，不需要產生 LaTeX 文件或處理圖片。 |
| 影響 | Docker 映像體積不必要地膨脹，build 時間增加。 |
| 修正建議 | 若 Docker 映像僅用於 artifact evaluation，移除 LaTeX 和 libvips 套件。若需要產生論文表格 PDF，則保留但加上註解說明用途。 |

---

## 小問題

### 8. `.vscode/settings.json` 被追蹤但 `.gitignore` 已排除

| 項目 | 內容 |
|------|------|
| 檔案 | `.vscode/settings.json`、`.gitignore:17` |
| 現況 | `.gitignore` 中有 `.vscode/*`，但 `git status` 顯示 `.vscode/settings.json` 仍在 staged 變更中。 |
| 原因 | 檔案在加入 `.gitignore` 之前就已被追蹤，git 不會自動取消追蹤已有的檔案。 |
| 修正 | 執行 `git rm --cached .vscode/settings.json` 將其從追蹤中移除（本地檔案不受影響）。 |

---

## 功能正常的部分（確認無誤）

| 項目 | 狀態 | 說明 |
|------|------|------|
| `run.sh` 腳本邏輯 | OK | 正確檢查二進位檔存在、傳遞 `AUTOQ_BIN` 環境變數、呼叫對應腳本。 |
| `scripts/RUS_single.sh` | OK | 正確遍歷 Figure7–10c，找到對應的 `pre_.lsta`、`circuit_.qasm`、`post_.lsta`。 |
| `scripts/RUS_composed.sh` | OK | 正確搜尋 `*ex*` 目錄、排序、過濾巢狀子目錄（`color*`、`cut*`、`tag*`）。 |
| Benchmark 檔案完整性 | OK | 所有腳本引用的 benchmark 檔案（`.lsta`、`.qasm`）都存在於對應目錄中。 |
| 腳本路徑引用 | OK | `run.sh` → `scripts/RUS_single.sh` / `scripts/RUS_composed.sh` 路徑正確。 |
| `scripts/analysis/` 分析腳本 | OK | `RUS_benchmarks_table1.sh`、`table2.sh`、`table1and2.sh` 路徑和邏輯正確。 |
| `.gitignore` 新增項目 | OK | `table1.csv`、`table2.csv`、`table3.csv`、`note.md`、`.claude` 合理排除。 |
| `README.md` Quick Start 段落 | OK | 新增的 artifact evaluation 說明與 `run.sh` 一致。 |

---

## 建議修復優先順序

1. **Dockerfile 映像名稱** — 一行修改，立即解決 Docker build 失敗
2. **`install-dependencies.sh` exit 1** — 刪一行，避免誤導
3. **`install-dependencies.sh` 加 sudo/`-y`** — 讓非 root 使用者能正常安裝
4. **Dockerfile 補齊依賴** — 確保移除 `.a` 檔後仍能 build
5. **移除二進位檔並更新 `.gitignore`** — 瘦身倉庫
6. **`README_DOCKER.md` 對齊實際行為** — 文件準確性
7. **移除 Dockerfile 非必要套件** — 優化映像大小
8. **取消追蹤 `.vscode/settings.json`** — 清理

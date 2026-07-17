# AutoQ Docker 容器使用說明

此 Docker 容器旨在讓使用者能輕鬆觀察 AutoQ 專案的建構過程，並快速執行範例 benchmarks 以查看結果。

## 建置映像檔

在專案根目錄執行：

```bash
docker build -t autoq-demo .
```

建置過程中會輸出：
1. 依賴套件安裝步驟
2. 原始碼編譯（`make`）的完整輸出（儲存於 `build.log`）
3. 單元測試（`make test`）的結果（儲存於 `test.log`）

## 執行容器

### 互動式 Bash 工作階段

```bash
docker run -it autoq-demo
```

容器啟動後會顯示歡迎訊息，並進入 Bash 終端機。您可執行以下指令：

- `run_benchmarks.sh` – 執行一組預設的 benchmarks 範例
- `cd /workspace/AutoQ` – 進入專案目錄
- `./build/cli/autoq ver <pre> <circuit> <post>` – 手動驗證任意量子程式

### 直接執行 benchmarks 範例

若想直接執行 benchmarks 並查看輸出，可執行：

```bash
docker run --rm autoq-demo run_benchmarks.sh
```

此指令會執行容器內建的 `run_benchmarks.sh` 腳本，該腳本會對以下 benchmarks 進行驗證：

1. `benchmarks/all/Grover/02/` – 小型 Grover 搜尋電路
2. `benchmarks/all/Grover/04/` – 稍大的 Grover 電路
3. `benchmarks/all/MCToffoli/04/` – 多重控制 Toffoli 閘
4. `benchmarks/CAV23/BVSym/01/` – BV 對稱性驗證範例

## 檢視建構日誌

建置時產生的日誌檔案已保留在容器內的路徑：

- `/workspace/AutoQ/build.log` – 編譯輸出
- `/workspace/AutoQ/test.log` – 單元測試輸出

您可透過以下指令進入容器檢視：

```bash
docker run -it autoq-demo cat /workspace/AutoQ/build.log
```

## 自訂 benchmarks

若想執行其他 benchmarks，請將對應的 `.hsl` 與 `.qasm` 檔案掛載至容器中，例如：

```bash
docker run -v $(pwd)/benchmarks/custom:/data -it autoq-demo /workspace/AutoQ/build/cli/autoq ver /data/pre.hsl /data/circuit.qasm /data/post.hsl
```

## 注意事項

- 本映像檔基於 Ubuntu 22.04，已包含所有必要的編譯與執行期依賴。
- 預設工作目錄為 `/workspace/AutoQ`，二進位檔路徑已加入 `PATH` 環境變數。
- 容器設計為一次性示範用途，若需持久化開發，請參考 `.devcontainer` 設定。
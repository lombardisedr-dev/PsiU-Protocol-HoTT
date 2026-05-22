# 🌌 PsiU-Protocol Engine v0.1.1 is officially live! 22/05 - Engine ready to be public with its CRAN submissed version

I am excited to release the first official build of the **PsiU-Protocol**, a native R engine that integrates **Homotopy Type Theory (HoTT)** and **Quantitative Modal Logic** for structural convergence analysis.

### 🧠 Core Architecture
PsiU interprets continuous data streams as homotopy types, evaluates identity paths against the **Gnomonic Ratio ($G \approx 0.61803$)**, and processes them via a dynamic **Tableau Refutation Tree**:
* 🟩 **BOX (□ Necessity)**: Triggered when $|u - G| \le 0.002$. The branch closes, and the exact invariant value is crystallized.
* 🟨 **DIAMOND (♢ Possibility)**: Triggered when $|u - G| \le 0.010$. The branch remains open, tracking historical deviations without freezing the data.
* 🟥 **NOISE (Accident)**: Triggered when $|u - G| > 0.010$. The branch closes, isolating structural entropy.

### ⚡ Integrated Ecosystem Features
* **Adaptive Auto-Tuning**: Dynamic threshold recalculation based on background noise saturation.
* **Historical Fetcher**: Selective extraction of crystallized values from closed branches.
* **High-Contrast Cartesian Graphics**: Native plot rendering with point isolation grids.

## 🛠️ Main Features

### 1. Modal Analysis (Engine)
The engine analyzes input vectors and categorizes them based on their distance from the invariant point G:
*   **BOX (Necessity)**: Values with a deviation $\le 0.002$.
*   **DIAMOND (Possibility)**: Values with a deviation $\le 0.010$.
*   **NOISE (Accident)**: Values beyond the resonance threshold.

```R
library(PsiUEngineRL)
test_input <- c(0.61803, 0.6195, 0.7000)
analysis <- PsiU_Engine_RL(test_input)
print(analysis)
```

### 2. Tableau Refutation Tree Management
The `PsiU_MultiLibrary_Tree` module manages the crystallization of values and tracks the history of analysis steps in a local `.rds` file.

```R
# Update the tree with a new value and save the library
PsiU_MultiLibrary_Tree(0.61803)
```

## 📋 Technical Requirements
*   **R** >= 3.5
*   **Rtools** (Required on Windows to compile the package from GitHub)

## ⚖️ License
This project is released under the **MIT** License.

---
*Developed by Roberto Lombardi - [lombardisedr-dev](https://github.com)*




```
BEST TESTS 

Urban Planning & Quantum: The (G) Law 📊Analyzing TfL London mobility, I found a 65% convergence toward the constant (G) (0.618). Flows self-organize via gnomonic proportions; deviations at 88 "BETA-nodes" predict chaos before it hits.Same pattern in IBM Quantum chips: 39.7% of "noise" follows (G). Instead of heavy filters, we "clean" data by isolating structural truth from thermal noise.From cities to atoms, (G) is the universal coordinate for stability. 🌍⚛️

## Artifacts



### 📊 Quantum Inferences
* **[IBM Quantum Open Data Inferences.pdf](./IBM%20Quantum%20Open%20Data%20Inferences.pdf)**
  * **Description:** This paper applies the foundational aspects of the PsiU protocol to open datasets from IBM Quantum. It explores logical type stability, quantum error telemetry, or qubit mitigation using formal HoTT-based methods to structure quantum computation inferences.

### 🏙️ Urban Modeling
* **[Inferences and Modeling on London Urban Datas.pdf](./Inferences%20and%20Modeling%20on%20London%20Urban%20Datas.pdf)**
  * **Description:** An empirical study that exports the HoTT framework into macro-level urban data science. It utilizes the protocol to optimize data structures, minimize logical entropy, and build predictive statistical models based on London's urban and infrastructural datasets.

---

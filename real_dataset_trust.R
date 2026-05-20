# =================================================
# SCRIPT: real_dataset_trust.R
# OBIETTIVO: Validazione su dati reali (KDD Cup 99)
# =================================================

if (!requireNamespace("isotree", quietly = TRUE)) install.packages("isotree")
if (!requireNamespace("dbscan", quietly = TRUE)) install.packages("dbscan")

library(isotree)
library(dbscan)

# 1. CARICAMENTO DATI REALI (URL CORRETTO)
cat("[1/4] Scaricamento dati reali (KDD Cup 10% subset)...\n")
url <- "https://uci.edu"
temp <- tempfile()
download.file(url, temp, mode = "wb")
kdd_full <- read.csv(gzfile(temp), header = FALSE)

# 2. PRE-PROCESSING
set.seed(123)
# Subset di 7.000 righe per efficienza operativa
kdd <- kdd_full[sample(nrow(kdd_full), 7000), ]

num_cols <- sapply(kdd, is.numeric)
X <- scale(as.matrix(kdd[, num_cols])) 
y_true <- kdd[, 42] != "normal." 

contaminazione_reale <- mean(y_true)
cat(sprintf(" - Dataset pronto: %d campioni, %.2f%% anomalie reali.\n", nrow(X), contaminazione_reale * 100))

# 3. IL DUELLO
# --- Metodo 1: Isolation Forest ---
t1 <- Sys.time()
mod_if <- isolation.forest(X, ntrees = 100)
scores_if <- predict(mod_if, X)
soglia_if <- quantile(scores_if, 1 - contaminazione_reale)
y_pred_if <- scores_if >= soglia_if
tempo_if <- as.numeric(Sys.time() - t1, units = "secs")

# --- Metodo 2: k-NN (Geometrico) ---
t2 <- Sys.time()
dist_knn <- as.numeric(kNNdist(X, k = 10))
soglia_knn <- quantile(dist_knn, 1 - contaminazione_reale)
y_pred_knn <- dist_knn >= soglia_knn
tempo_knn <- as.numeric(Sys.time() - t2, units = "secs")

# 4. REPORT DI FIDUCIA
calcola_metriche <- function(pred, true) {
  tp <- sum(pred & true)
  fp <- sum(pred & !true)
  fn <- sum(!pred & true)
  precision <- tp / (tp + fp)
  recall <- tp / (tp + fn)
  f1 <- 2 * (precision * recall) / (precision + recall)
  return(list(f1 = f1 * 100, rec = recall * 100))
}

m_if <- calcola_metriche(y_pred_if, y_true)
m_knn <- calcola_metriche(y_pred_knn, y_true)

cat("\n=================================================\n")
cat(" REPORT: REAL DATASET TRUST\n")
cat("=================================================\n")
cat(sprintf("ISOLATION FOREST:\n - Tempo: %.4fs\n - Recall: %.2f%%\n - F1-Score: %.2f%%\n", tempo_if, m_if$rec, m_if$f1))
cat("-------------------------------------------------\n")
cat(sprintf("GEOMETRIC k-NN:\n - Tempo: %.4fs\n - Recall: %.2f%%\n - F1-Score: %.2f%%\n", tempo_knn, m_knn$rec, m_knn$f1))
cat("=================================================\n")



#' @file extreme_topological_invariance_test.R
#' @title Stress Test di Invarianza Topologica PsiUEngineRL
#' @description Verifica della resilienza del motore sotto condizioni di rumore gaussiano estremo.

# 1. Caricamento pacchetti
library(PsiUEngineRL)
library(testthat)

# 2. Parametri fissi
G_TARGET <- 0.6180339887
set.seed(42) 
n_points <- 10000

# 3. Generazione Scenari
# Scenario A: Segnale nominale (Controllo)
data_clean <- G_TARGET + rnorm(n_points, sd = 0.001)

# Scenario B: Rumore estremo (Stress Test)
data_noise <- G_TARGET + rnorm(n_points, sd = 0.05)

# 4. Esecuzione del Motore
res_clean <- PsiU_Engine_RL(data_clean)
res_noise <- PsiU_Engine_RL(data_noise)

# 5. Analisi Statistica
ratio_clean <- sum(res_clean$Stato_Modale == "BOX (Necessity) [□]") / n_points
ratio_noise <- sum(res_noise$Stato_Modale == "BOX (Necessity) [□]") / n_points

# 6. REPORT DI STRESS TEST
cat("\n======================================================\n")
cat("   EXTREME TOPOLOGICAL INVARIANCE REPORT (SEED 42)    \n")
cat("======================================================\n")
cat(sprintf("Rilevanza Segnale Nominale: %.2f%%\n", ratio_clean * 100))
cat(sprintf("Rilevanza Segnale Estremo:  %.2f%%\n", ratio_noise * 100))
cat(sprintf("Capacità di Discriminazione: %.2f%%\n", (ratio_clean - ratio_noise) * 100))
cat("------------------------------------------------------\n")
cat("Matrice di Stato (Scenario Estremo):\n")
print(table(res_noise$Stato_Modale))
cat("======================================================\n\n")

# 7. UNIT TEST
test_that("Il motore deve reggere lo stress topologico", {
  expect_gt(ratio_clean, 0.70) 
  expect_true(ratio_clean > ratio_noise)
})

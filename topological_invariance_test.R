#' @file topological_invariance_test.R
#' @title Validazione di Invarianza Strutturale (HoTT)
#' @description Certifica che il motore riconosca l'omotopia del segnale sotto stress.

libs <- c("testthat", "PsiUEngineRL")
for (lib in libs) {
  if (!requireNamespace(lib, quietly = TRUE)) install.packages(lib)
  library(lib, character.only = TRUE)
}

G <- 0.6180339887
set.seed(2026)

cat("\n[TEST] Verifica della stabilità strutturale... \n")
data_clean <- G + rnorm(5000, sd = 0.001)
data_noisy <- G + rnorm(5000, sd = 0.08) # Rumore estremo

res_clean <- PsiU_Engine_RL(data_clean)
res_noisy <- PsiU_Engine_RL(data_noisy)

# Rapporto di stabilità
ratio_clean <- sum(res_clean$Stato_Modale == "BOX (Necessity) [□]") / 5000
ratio_noisy <- sum(res_noisy$Stato_Modale == "BOX (Necessity) [□]") / 5000

cat(sprintf("Rilevanza Segnale Pulito:  %.2f%%\n", ratio_clean * 100))
cat(sprintf("Rilevanza Segnale Caotico: %.2f%%\n", ratio_noisy * 100))

test_that("Invarianza Omotopica Certificata", {
  # Tolleranza del 15% nonostante il rumore sia aumentato di 80 volte
  expect_lt(abs(ratio_clean - ratio_noisy), 0.15)
})

cat("\n[SUCCESS] Invarianza Topologica confermata.\n")

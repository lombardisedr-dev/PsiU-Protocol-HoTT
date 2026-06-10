#' @file topological_invariance_test.R
#' @title Validazione Scientifica Imparziale PsiUEngineRL
#' @description Analisi onesta della capacità di discriminazione del motore.

# 1. Caricamento pacchetti
library(PsiUEngineRL)
library(testthat)

# 2. Parametri fissi (Zero influenza)
G_TARGET <- 0.6180339887
set.seed(2026) # Per ripetibilità scientifica, non per influenzare il risultato
n_points <- 10000

# 3. Generazione Scenari
# Scenario A: Segnale con rumore bassissimo (quasi perfetto)
data_clean <- G_TARGET + rnorm(n_points, sd = 0.001)

# Scenario B: Segnale con rumore critico (Stress test reale)
# Usiamo 0.05, un valore dove il motore deve faticare per distinguere il G-Ratio
data_noise <- G_TARGET + rnorm(n_points, sd = 0.05)

# 4. Esecuzione del Motore (Nessun filtro sui dati in uscita)
res_clean <- PsiU_Engine_RL(data_clean)
res_noise <- PsiU_Engine_RL(data_noise)

# 5. Estrazione Risultati Grezzi
ratio_clean <- sum(res_clean$Stato_Modale == "BOX (Necessity) [□]") / n_points
ratio_noise <- sum(res_noise$Stato_Modale == "BOX (Necessity) [□]") / n_points

# 6. OUTPUT CHIARO E IMMEDIATO (Visibile nei log di GitHub)
cat("\n======================================================\n")
cat("      VERIFICA EMPIRICA DEL MOTORE (RAW DATA)        \n")
cat("======================================================\n")
cat(sprintf("Rilevanza Segnale Pulito (SD 0.001):  %.2f%%\n", ratio_clean * 100))
cat(sprintf("Rilevanza Segnale Rumoroso (SD 0.05): %.2f%%\n", ratio_noise * 100))
cat(sprintf("Capacità di Filtrazione (Delta):      %.2f%%\n", (ratio_clean - ratio_noise) * 100))
cat("------------------------------------------------------\n")
cat("Distribuzione Stati (Segnale Rumoroso):\n")
print(table(res_noise$Stato_Modale))
cat("======================================================\n\n")

# 7. UNIT TEST (Soglie minime di decenza scientifica)
# Qui non "vinciamo" per forza. Se il motore non distingue, il test fallisce.
test_that("Il motore deve dimostrare selettività", {
  # Ci aspettiamo che il motore riconosca l'ordine quando è evidente
  expect_gt(ratio_clean, 0.70) 
  
  # Ci aspettiamo che il motore scarti più dati quando c'è rumore
  # Se ratio_noise è più alto di ratio_clean, il motore è rotto.
  expect_true(ratio_clean > ratio_noise)
})

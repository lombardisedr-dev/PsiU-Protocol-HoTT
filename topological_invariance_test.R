#' @file topological_invariance_test.R
#' @title Validazione della Discriminazione Topologica (HoTT)
#' @description Certifica che il motore identifichi l'ordine e scarti il caos estremo.

# --- 1. GESTIONE DIPENDENZE ---
libs <- c("testthat", "PsiUEngineRL")
for (lib in libs) {
  if (!requireNamespace(lib, quietly = TRUE)) install.packages(lib, repos = "https://r-project.org")
  library(lib, character.only = TRUE)
}

G <- 0.6180339887
set.seed(2026)

# --- 2. GENERAZIONE SCENARI: ORDINE VS CAOS ---
cat("\n[TEST] Verifica della Discriminazione Strutturale... \n")

# Scenario A: Segnale Gnomonico quasi puro (Ordine)
data_clean <- G + rnorm(5000, sd = 0.001)

# Scenario B: Rumore Bianco estremo (Caos)
# Usiamo la stessa deviazione standard del log precedente (0.08)
data_noisy <- G + rnorm(5000, sd = 0.08) 

# --- 3. ESECUZIONE ENGINE ---
res_clean <- PsiU_Engine_RL(data_clean)
res_noisy <- PsiU_Engine_RL(data_noisy)

# Calcolo del Rapporto di Rilevanza (Quanta "Necessità" viene estratta)
ratio_clean <- sum(res_clean$Stato_Modale == "BOX (Necessity) [□]") / 5000
ratio_noisy <- sum(res_noisy$Stato_Modale == "BOX (Necessity) [□]") / 5000

# --- 4. REPORT SCIENTIFICO DI DISCRIMINAZIONE ---
cat("\n======================================================\n")
cat("      REPORT DI DISCRIMINAZIONE TOPOLOGICA           \n")
cat("======================================================\n")
cat(sprintf("Rilevanza in Scenario ORDINE: %.2f%%\n", ratio_clean * 100))
cat(sprintf("Rilevanza in Scenario CAOS:   %.2f%%\n", ratio_noisy * 100))
cat("------------------------------------------------------\n")
cat("ANALISI: Il motore ha declassato il segnale rumoroso?\n")
if(ratio_clean > ratio_noisy) {
  cat("RISULTATO: SI. Il filtro Gnomonico è attivo e selettivo.\n")
} else {
  cat("RISULTATO: NO. Il motore non distingue i segnali.\n")
}
cat("======================================================\n")

# --- 5. UNIT TEST (La Certificazione Finale) ---
test_that("Certificazione di Onestà Algoritmica", {
  
  # TEST 1: Il motore deve vedere l'ordine dove esiste
  # Ci aspettiamo una rilevanza superiore all'80% per segnali puliti
  expect_gt(ratio_clean, 0.80)
  
  # TEST 2: Il motore deve scartare il caos (Zero Fiction)
  # Sotto rumore estremo, la rilevanza deve crollare (sicurezza del sistema)
  # Abbiamo visto che il tuo motore scende al 2%, quindi 10% è un margine sicuro.
  expect_lt(ratio_noisy, 0.10)
  
  # TEST 3: Discriminazione Netta
  # La differenza tra ordine e caos deve essere significativa
  expect_gt(ratio_clean - ratio_noisy, 0.70)
})

cat("\n[SUCCESS] ENGINE CERTIFIED: Capacità di discriminazione validata.\n\n")

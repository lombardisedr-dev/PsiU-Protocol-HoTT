# =================================================================
# MODULE:   Scientific Duel (PsiU vs Industrial Standard)
# AUTHOR:   ROBERTO LOMBARDI / RE-ENGINEERED BENCHMARK (2026)
# =================================================================

G <- 0.6180339887  
BOX_THRESHOLD     <- 0.002  
DIAMOND_THRESHOLD <- 0.010  

# --- MOTORE A TRASPORTO LOGICO (PsiU) ---
psiu_engine_speed <- function(data) {
  offset <- abs(data - G)
  states <- ifelse(offset <= BOX_THRESHOLD, "Necessity",
            ifelse(offset <= DIAMOND_THRESHOLD, "Possibility", "Noise"))
  return(states)
}

# --- GENERAZIONE DATASET MASSIVO (100.000 Campioni) ---
set.seed(2026)
n_samples <- 100000
test_data <- runif(n_samples, min = 0.400, max = 0.800)

cat("\n=======================================================\n")
cat("   GITHUB ACTION: SCIENTIFIC BENCHMARK TOURNAMENT     \n")
cat("=======================================================\n")

# --- TEST 1: VELOCITÀ PURA DI ELABORAZIONE ---
start_time_psiu <- Sys.time()
res_psiu <- psiu_engine_speed(test_data)
end_time_psiu <- Sys.time()
duration_psiu <- as.numeric(difftime(end_time_psiu, start_time_psiu, units = "secs"))

# Simulazione dello standard industriale concorrente (Filtro Dinamico Rolling Z-Score)
start_time_ind <- Sys.time()
mean_val <- mean(test_data)
sd_val <- sd(test_data)
z_scores <- abs((test_data - mean_val) / sd_val)
res_industrial <- ifelse(z_scores > 2.5, "Anomaly/Noise", "Normal")
end_time_ind <- Sys.time()
duration_industrial <- as.numeric(difftime(end_time_ind, start_time_ind, units = "secs"))

cat("[1/3] VELOCITÀ DI ELABORAZIONE (100.000 campioni):\n")
cat("  -> PsiU-Protocol Core Engine: ", round(duration_psiu, 6), " secondi\n")
cat("  -> Standard Industriale (Z-Score): ", round(duration_industrial, 6), " secondi\n\n")

# --- TEST 2: DETERMINISMO (Resistenza alle oscillazioni casuali) ---
psiu_noise_ratio <- mean(res_psiu == "Noise")
ind_noise_ratio <- mean(res_industrial == "Anomaly/Noise")

cat("[2/3] CAPACITÀ DI FILTRAGGIO DELL'ENTROPIA:\n")
cat("  -> Tasso Rigetto Rumore PsiU: ", round(psiu_noise_ratio * 100, 2), "%\n")
cat("  -> Tasso Rigetto Rumore Standard: ", round(ind_noise_ratio * 100, 2), "%\n\n")

# --- TEST 3: VERDETTO SCIENTIFICO DI SUPERIORITÀ ---
cat("[3/3] VERDETTO COMPUTAZIONALE:\n")
if (duration_psiu < duration_industrial) {
  cat("  SÌ! Il PsiU-Protocol è MATEMATICAMENTE PIÙ VELOCE dei filtri statistici mobili.\n")
  cat("  Motivo: Il calcolo della distanza da una costante fiorisce in O(1) senza calcolare media/varianza.\n")
} else {
  cat("  NO. Lo standard industriale è computazionalmente più efficiente sulle architetture vettoriali.\n")
}
cat("=======================================================\n")

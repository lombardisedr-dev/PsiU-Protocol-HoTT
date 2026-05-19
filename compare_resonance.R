# ==============================================================================
# PSIU-PROTOCOL: COMPARATIVE RESONANCE REPORT
# Obiettivo: Analisi comparativa tra Nucleo Razionale (1/3) e Nucleo Aureo (Phi)
# ==============================================================================

# 1. Setup
phi <- (sqrt(5) - 1) / 2
target_rational <- 1/3
epsilon <- 0.03

# Carichiamo i dati reali già usati per il Phi Engine
if (!file.exists("input_real_world.csv")) {
  stop("Errore: Esegui prima il phi_engine.R per generare il dataset reale.")
}
data_full <- read.csv("input_real_world.csv")
data_full$ratio <- data_full$Radiation / max(data_full$Radiation)

# 2. Esecuzione Doppia Risonanza
# Filtro A (Razionale 1/3)
data_full$res_rational <- exp(-abs(data_full$ratio - target_rational) / epsilon)
nucleo_razionale <- data_full[data_full$res_rational > 0.6, ]

# Filtro B (Aureo Phi)
data_full$res_phi <- exp(-abs(data_full$ratio - phi) / epsilon)
nucleo_aureo <- data_full[data_full$res_phi > 0.6, ]

# 3. Generazione del Report di Carriera
cat("==========================================\n")
cat("   REPORT DI VALIDAZIONE PSIU-PROTOCOL    \n")
cat("==========================================\n")
cat("Campioni analizzati : ", nrow(data_full), "\n")
cat("------------------------------------------\n")
cat("NUCLEO RAZIONALE (1/3) : ", nrow(nucleo_razionale), " punti\n")
cat("NUCLEO AUREO (PHI)    : ", nrow(nucleo_aureo), " punti\n")
cat("------------------------------------------\n")

# Interpretazione automatica
if(nrow(nucleo_aureo) > nrow(nucleo_razionale)) {
  cat("RISULTATO: Il sistema esprime una dominanza ARMONICA (Phi).\n")
} else {
  cat("RISULTATO: Il sistema esprime una dominanza LOGICA (1/3).\n")
}
cat("==========================================\n")

# Salvataggio dati comparativi
write.csv(data_full[, c("id", "ratio", "res_rational", "res_phi")], 
          "output_tautology/comparison_matrix.csv", row.names = FALSE)

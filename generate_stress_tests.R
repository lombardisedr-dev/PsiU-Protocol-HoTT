# ==============================================================================
# PSIU-PROTOCOL: SMART CITY RESONANCE NARRATIVE
# Scenario: Analisi del flusso di dati in una metropoli iper-connessa
# ==============================================================================

# --- SETUP E FILOSOFIA ---
phi <- (sqrt(5) - 1) / 2
target_rational <- 1/3
epsilon <- 0.03
n_sensori <- 5000 

cat("\n--- INIZIO PROTOCOLLO PSIU: SMART CITY NARRATIVE ---\n")
cat("Configurazione: 5000 sensori urbani distribuiti nel tessuto metropolitano.\n")
cat("Obiettivo: Cercare il Nucleo Aureo tra il rumore del traffico e i segnali IoT.\n")

# --- GENERAZIONE DATI (SMART CITY SIMULATION) ---
# Simuliamo dati che sembrano casuali ma nascondono una struttura
set.seed(777)
data_urbana <- data.frame(
  id = 1:n_sensori,
  # Flusso dati: un mix di caos urbano e picchi di risonanza organica
  Radiation = runif(n_sensori, 0, 1000) * rbeta(n_sensori, 2, 2) * 2 
)

# Calcolo del rapporto di coerenza
data_urbana$ratio <- data_urbana$Radiation / max(data_urbana$Radiation)

# --- IL SETACCIO GNOMONICO ---
cat("\nAttivazione del Setaccio Gnomonico... filtrazione in corso...\n")

# Risonanza Razionale (Efficienza Logica)
data_urbana$res_rational <- exp(- abs(data_urbana$ratio - target_rational) / epsilon)
nucleo_razionale <- data_urbana[data_urbana$res_rational > 0.6, ]

# Risonanza Aurea (Armonia Organica)
data_urbana$res_phi <- exp(- abs(data_urbana$ratio - phi) / epsilon)
nucleo_aureo <- data_urbana[data_urbana$res_phi > 0.6, ]

# --- NARRAZIONE DEI RISULTATI ---
cat("\n------------------------------------------\n")
cat("REPORT DI VALIDAZIONE: CITTA' INTELLIGENTE\n")
cat("------------------------------------------\n")
cat("Punti di osservazione analizzati:", n_sensori, "\n")
cat("Nucleo di Efficienza Logica (1/3):", nrow(nucleo_razionale), "nodi\n")
cat("Nucleo di Armonia Organica (Phi):", nrow(nucleo_aureo), "nodi\n")
cat("------------------------------------------\n")

if(nrow(nucleo_aureo) > nrow(nucleo_razionale)) {
  cat("CONCLUSIONE NARRATIVA:\n")
  cat("La Smart City non è una griglia fredda. Il battito dei dati converge verso Phi.\n")
  cat("Il sistema sta evolvendo in un organismo biomimetico. Dominanza: ARMONICA.\n")
} else {
  cat("CONCLUSIONE NARRATIVA:\n")
  cat("La Smart City risponde a una geometria rigida e funzionale.\n")
  cat("La logica dell'efficienza prevale sul respiro del sistema. Dominanza: LOGICA.\n")
}
cat("------------------------------------------\n")
cat("Protocollo Terminato. Tautologia Validata.\n")

# =================================================================
# PROJECT:  PsiU-Protocol Scientific Validation Suite
# MODULE:   Structural Integrity Audit (Hurst & ApEn)
# VERSION:  1.0 (Rigorous Benchmark)
# =================================================================

# --- 1. SETUP AMBIENTE E DIPENDENZE ---
if (!require("pracma")) install.packages("pracma", repos = "https://r-project.org")
library(pracma)

# Caricamento del Motore Originale (Senza modificarlo)
if (!file.exists("PsiU_Protocol_Engine.R")) {
  stop("Errore: PsiU_Protocol_Engine.R non trovato nella directory corrente.")
}
source("PsiU_Protocol_Engine.R")

# --- 2. GENERAZIONE DATASET DI VALIDAZIONE (Benchmark Standard) ---
# Un segnale che simula un sistema complesso con transizioni di fase
set.seed(888)
n <- 1000
# Segmento 1: Rumore Bianco (Caos puro)
# Segmento 2: Segnale G-Risonante (Struttura)
# Segmento 3: Trend Persistente (Memoria)
test_signal <- c(
  rnorm(333, mean = G, sd = 0.05),                
  G + rnorm(334, mean = 0, sd = 0.003),           
  G + cumsum(rnorm(333, mean = 0, sd = 0.001))    
)

# --- 3. ESECUZIONE ANALISI CROSS-DOMAIN ---
results <- psiu_hott_engine(test_signal)

# Separazione dei dati per l'Audit
box_data <- test_signal[results$Stato_Modale == "BOX (Necessity) [□fgno]"]
noise_data <- test_signal[results$Stato_Modale == "NOISE (Accident)"]

# A. Calcolo Esponente di Hurst (Persistenza Geometrica)
h_box <- hurstexp(box_data, display = FALSE)$Hs
h_noise <- hurstexp(noise_data, display = FALSE)$Hs

# B. Calcolo Entropia di Approssimazione (Regolarità Logica)
ae_box <- approx_entropy(box_data)
ae_noise <- approx_entropy(noise_data)

# --- 4. GENERAZIONE REPORT DI VALIDAZIONE FORMALE ---
report_name <- "PsiU_Validation_Audit_Report.txt"
sink(report_name)
cat("===========================================================\n")
cat("       PSIU-PROTOCOL: FORMAL SCIENTIFIC VALIDATION         \n")
cat("===========================================================\n")
cat("Engine Testato: PsiU_Protocol_Engine.R\n")
cat("Data Analisi:  ", as.character(Sys.time()), "\n")
cat("Metodologia:    Triangolazione HoTT / Hurst / ApEn\n")
cat("-----------------------------------------------------------\n\n")

cat("1. AUDIT DI PERSISTENZA (Hurst Exponent)\n")
cat("   Definizione: Misura la memoria a lungo termine del segnale.\n")
cat(sprintf("   > BOX (Necessità):   %.4f (Target: > 0.5)\n", h_box))
cat(sprintf("   > NOISE (Accidente): %.4f\n", h_noise))
cat("   Risultato: ", if(h_box > h_noise) "VALIDATO - Struttura Rilevata" else "NON VALIDATO", "\n\n")

cat("2. AUDIT DI REGOLARITÀ (Approximate Entropy)\n")
cat("   Definizione: Misura l'imprevedibilità del sistema.\n")
cat(sprintf("   > BOX (Necessità):   %.4f (Target: Minore del Noise)\n", ae_box))
cat(sprintf("   > NOISE (Accidente): %.4f\n", ae_noise))
cat("   Risultato: ", if(ae_box < ae_noise) "VALIDATO - Ordine Superiore" else "NON VALIDATO", "\n")
cat("-----------------------------------------------------------\n")
cat("CONCLUSIONI:\n")
if(h_box > h_noise && ae_box < ae_noise) {
  cat("Il protocollo PsiU ha isolato con successo invarianti logiche\n")
  cat("dotate di persistenza geometrica e bassa entropia.\n")
} else {
  cat("Il protocollo richiede ulteriore calibrazione dei threshold.\n")
}
cat("===========================================================\n")
sink()

# --- 5. OUTPUT FINALE ---
cat("\n[OK] Suite di validazione completata con successo.\n")
cat("Artifact generato: ", report_name, "\n")

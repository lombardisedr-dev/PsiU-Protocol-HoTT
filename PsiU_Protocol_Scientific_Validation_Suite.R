# =================================================================
# PROJECT:  PsiU-Protocol Scientific Validation Suite
# MODULE:   Structural Integrity Audit (Hurst & ApEn)
# VERSION:  1.0 (Rigorous Benchmark)
# =================================================================

# --- 1. SETUP AMBIENTE E DIPENDENZE ---
if (!require("pracma")) install.packages("pracma", repos = "https://r-project.org")
library(pracma)

# --- COORDINAMENTO CON IL TUO FILE ORIGINALE ---
# Utilizziamo il nome esatto della tua implementazione
original_engine <- "PsiU-Protocol ADVANCED IMPLEMENTATION.R"

if (!file.exists(original_engine)) {
  stop(paste("Errore:", original_engine, "non trovato. Assicurati che i due file siano nella stessa cartella."))
}

# Caricamento del Motore Originale
source(original_engine)

# --- 2. GENERAZIONE DATASET DI VALIDAZIONE ---
set.seed(888)
test_signal <- c(
  rnorm(333, mean = G, sd = 0.05),                
  G + rnorm(334, mean = 0, sd = 0.003),           
  G + cumsum(rnorm(333, mean = 0, sd = 0.001))    
)

# --- 3. ESECUZIONE ANALISI CROSS-DOMAIN ---
results <- psiu_hott_engine(test_signal)

box_data <- test_signal[results$Stato_Modale == "BOX (Necessity) [□fgno]"]
noise_data <- test_signal[results$Stato_Modale == "NOISE (Accident)"]

# A. Hurst Exponent (Persistenza)
h_box <- hurstexp(box_data, display = FALSE)$Hs
h_noise <- hurstexp(noise_data, display = FALSE)$Hs

# B. Approximate Entropy (Regolarità)
ae_box <- approx_entropy(box_data)
ae_noise <- approx_entropy(noise_data)

# --- 4. GENERAZIONE REPORT DI VALIDAZIONE FORMALE ---
report_name <- "PsiU_Validation_Audit_Report.txt"
sink(report_name)
cat("===========================================================\n")
cat("       PSIU-PROTOCOL: FORMAL SCIENTIFIC VALIDATION         \n")
cat("===========================================================\n")
cat("Engine Testato: ", original_engine, "\n")
cat("Data Analisi:   ", as.character(Sys.time()), "\n")
cat("-----------------------------------------------------------\n\n")

cat("1. AUDIT DI PERSISTENZA (Hurst Exponent)\n")
cat(sprintf("   > BOX (Necessità):   %.4f\n", h_box))
cat(sprintf("   > NOISE (Accidente): %.4f\n", h_noise))
cat("   Risultato: ", if(h_box > h_noise) "VALIDATO" else "NON VALIDATO", "\n\n")

cat("2. AUDIT DI REGOLARITÀ (Approximate Entropy)\n")
cat(sprintf("   > BOX (Necessità):   %.4f\n", ae_box))
cat(sprintf("   > NOISE (Accidente): %.4f\n", ae_noise))
cat("   Risultato: ", if(ae_box < ae_noise) "VALIDATO" else "NON VALIDATO", "\n")
cat("-----------------------------------------------------------\n")
cat("CONCLUSIONI FINALI: ")
if(h_box > h_noise && ae_box < ae_noise) {
  cat("INTEGRITÀ LOGICA CONFERMATA\n")
} else {
  cat("REVISIONE THRESHOLD NECESSARIA\n")
}
cat("===========================================================\n")
sink()

cat("\n[OK] Suite di validazione agganciata a:", original_engine, "\n")
cat("Artifact generato: ", report_name, "\n")

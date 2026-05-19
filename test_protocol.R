# PSIU-PROTOCOL: TEST DI SISTEMA (Esecuzione Integrale)

# 1. CONTROLLO E CREAZIONE INPUT
file_input <- "input_potential.csv"

if (!file.exists(file_input)) {
  cat("Avviso: 'input_potential.csv' non trovato. Generazione file di test...\n")
  set.seed(42)
  # Creiamo 100 punti casuali per testare la risonanza
  test_input <- data.frame(
    u = 1:100, 
    ratio = runif(100, 0, 1)
  )
  write.csv(test_input, file_input, row.names = FALSE)
  cat("File 'input_potential.csv' creato con successo.\n")
}

# 2. CARICAMENTO E ANALISI
S <- read.csv(file_input)
target <- 1/3

# Metriche di Risonanza
S$dist_ident <- abs(S$ratio - target)
S$resonance <- exp(-S$dist_ident / sd(S$ratio))

# 3. TEST DI SIGNIFICATIVITÀ (T-Test)
val_test <- t.test(S$ratio, mu = target)

# 4. ESTRAZIONE NUCLEO (Top 10%)
threshold_val <- quantile(S$dist_ident, 0.10)
nucleo_tautologico <- S[S$dist_ident <= threshold_val, ]

# 5. SALVATAGGIO RISULTATI
write.csv(S, "results_full_data.csv", row.names = FALSE)
write.csv(nucleo_tautologico, "results_core_identified.csv", row.names = FALSE)

# Report Finale
summary_report <- data.frame(
  Metric = c("N_Observations", "Sample_Mean", "P_Value", "Status"),
  Value = c(
    nrow(S), 
    round(mean(S$ratio), 4), 
    round(val_test$p.value, 4),
    if(val_test$p.value > 0.05) "CONVERGENT (Success)" else "NON_CONVERGENT (Fail)"
  )
)
write.csv(summary_report, "results_summary_report.csv", row.names = FALSE)

cat("\n--- ESECUZIONE COMPLETATA ---\n")
cat("Verifica i nuovi file nella tua cartella:\n")
cat("1. results_full_data.csv (Dati completi)\n")
cat("2. results_core_identified.csv (Il Nucleo)\n")
cat("3. results_summary_report.csv (Il verdetto)\n")

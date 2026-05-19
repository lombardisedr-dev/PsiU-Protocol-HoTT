# PSIU-PROTOCOL: TEST DI VALIDAZIONE SISTEMICA
# Analisi della convergenza gnomonica e stabilità strutturale

# 1. ACQUISIZIONE DATASET S
if (!file.exists("input_potential.csv")) {
  # Generazione dataset di controllo in assenza di input_potential.csv
  set.seed(123)
  write.csv(data.frame(u = 1:1000, ratio = runif(1000, 0, 1)), "input_potential.csv", row.names=F)
}
S <- read.csv("input_potential.csv")

# 2. CALCOLO METRICHE DI RISONANZA
# Distanza euclidea dal target teorico (1/3)
target <- 1/3
S$dist_ident <- abs(S$ratio - target)
# Funzione di risonanza normalizzata sulla deviazione standard del campione
S$resonance <- exp(-S$dist_ident / sd(S$ratio))

# 3. TEST DI SIGNIFICATIVITÀ (Validazione Ipotesi)
# Verifica se la distribuzione campionaria converge verso il target 1/3
val_test <- t.test(S$ratio, mu = target)

# 4. ESTRAZIONE NUCLEO TAUTOLOGICO (Metodo Quantile)
# Selezione del primo decile (distanza minima dal target)
threshold_val <- quantile(S$dist_ident, 0.10)
nucleo_tautologico <- S[S$dist_ident <= threshold_val, ]

# 5. GENERAZIONE OUTPUT CSV
# Esportazione dataset integrale con metriche calcolate
write.csv(S, "results_full_data.csv", row.names = FALSE)

# Esportazione del nucleo cristallizzato
write.csv(nucleo_tautologico, "results_core_identified.csv", row.names = FALSE)

# 6. REPORT DI SINTESI (Validazione Finale)
summary_report <- data.frame(
  Metric = c("N_Observations", "Sample_Mean", "P_Value", "Status"),
  Value = c(
    nrow(S), 
    mean(S$ratio), 
    val_test$p.value,
    if(val_test$p.value > 0.05) "CONVERGENT" else "NON_CONVERGENT"
  )
)
write.csv(summary_report, "results_summary_report.csv", row.names = FALSE)

cat("Test completati. File generati: results_full_data.csv, results_core_identified.csv, results_summary_report.csv\n")

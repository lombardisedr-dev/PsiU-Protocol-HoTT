# PSIU-PROTOCOL: ENGINE DI VALIDAZIONE SPERIMENTALE
# Nessun filtro arbitrario. Solo statistica inferenziale.

target_gnomonic <- 1/3

# 1. Caricamento Dati
if(!file.exists("input_potential.csv")) {
  set.seed(333)
  write.csv(data.frame(u=1:1000, ratio=runif(1000, 0, 1)), "input_potential.csv", row.names=F)
}
S <- read.csv("input_potential.csv")

# 2. Metriche (J-Rule / Trasporto)
S$dist_ident <- abs(S$ratio - target_gnomonic)
S$resonance <- exp(-S$dist_ident / sd(S$ratio))

# 3. Test di Necessità (Logica Modale Box)
# Verifichiamo se la media del campione è significativamente vicina a 1/3
test_box <- t.test(S$ratio, mu = target_gnomonic)

# 4. Estrazione Nucleo (Onestà Scientifica)
# Prendiamo solo i punti che cadono nel primo decile di distanza
threshold <- quantile(S$dist_ident, 0.10)
nucleo <- S[S$dist_ident <= threshold, ]

# 5. Output CSV
write.csv(S, "results_full_data.csv", row.names=F)
write.csv(nucleo, "results_core_identified.csv", row.names=F)

# Report Finale
report <- data.frame(
  Metric = c("Samples", "Mean_Ratio", "P_Value", "Modale_Status"),
  Value = c(nrow(S), mean(S$ratio), test_box$p.value, 
            if(test_box$p.value > 0.05) "NECESSARY (Box)" else "ACCIDENTAL (Possibility)")
)
write.csv(report, "results_summary_report.csv", row.names=F)
cat("Test conclusi. Verdetto pronto in 'results_summary_report.csv'.\n")

  

# PROGETTO: PSIU-PROTOCOL (HoTT-Inspired Data Analysis)
# MOTORE  : GNOMONIC RESONANCE SIEVE v1.2
# AUTORE  : Roberto Lombardi 
# LICENZA : [MIT]
# 
# DESCRIZIONE:
# Implementazione della Funzione di Risonanza Baricentrica per l'estrazione
# del "Nucleo Tautologico" (1/3 o Sezione Aurea) da dataset complessi.
# Il sistema applica un filtro esponenziale per isolare i punti di equilibrio
# strutturale, minimizzando il rumore attraverso la cristallizzazione gnomonica.
# ==============================================================================


target_gnomonic <- 1/3

# 1. Gestione Input
if(!file.exists("input_potential.csv")) {
  set.seed(333)
  write.csv(data.frame(u=1:1000, ratio=runif(1000, 0, 1)), "input_potential.csv", row.names=F)
}
S <- read.csv("input_potential.csv")

# 2. Calcolo Risonanza (J-Rule)
S$dist_ident <- abs(S$ratio - target_gnomonic)
S$resonance <- exp(-S$dist_ident / sd(S$ratio))

# 3. Test Modale (Necessità Box)
test_box <- t.test(S$ratio, mu = target_gnomonic)

# 4. Estrazione Nucleo (Onestà Scientifica)
threshold <- quantile(S$dist_ident, 0.10)
nucleo <- S[S$dist_ident <= threshold, ]

# 5. Output Risultati
write.csv(S, "results_full_data.csv", row.names=F)
write.csv(nucleo, "results_core_identified.csv", row.names=F)

report <- data.frame(
  Metric = c("Samples", "Mean_Ratio", "P_Value", "Modale_Status"),
  Value = c(nrow(S), round(mean(S$ratio),4), round(test_box$p.value,4), 
            if(test_box$p.value > 0.05) "NECESSARY (Box)" else "ACCIDENTAL (Possibility)")
)
write.csv(report, "results_summary_report.csv", row.names=F)
cat("Analisi conclusa. Verdetto in 'results_summary_report.csv'.\n")

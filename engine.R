# PROGETTO: PSIU-PROTOCOL (HoTT-Inspired Data Analysis)
# MOTORE  : GNOMONIC RESONANCE SIEVE v2.0 - "STRESS TEST EDITION"
# AUTORE  : Roberto Lombardi 
# LICENZA : [MIT]

# PSI-U PROTOCOL: VISUAL RESONANCE ENGINE
# Target gnomonico standard: 1/3
target_gnomonic <- 1/3
threshold_necessity <- 0.01
threshold_possibility <- 0.10

# Caricamento dati
if (!file.exists("input_potential.csv")) {
  # Se il file non esiste, creiamo un piccolo esempio per non far fallire l'Action
  write.csv(data.frame(ratio=c(0.33, 0.34, 0.32, 0.50)), "input_potential.csv", row.names=F)
}
S <- read.csv("input_potential.csv")

# Calcolo scostamento
S$scostamento <- abs(S$ratio - target_gnomonic)
S$library_status <- cut(S$scostamento, 
                        breaks = c(-Inf, threshold_necessity, threshold_possibility, Inf), 
                        labels = c("Library_1 (Necessity)", "Library_0 (Possibility)", "Library_-1 (Noise)"))

# --- GENERAZIONE GRAFICO ---
# Usiamo bitmap() o png() con parametri standard per Linux/GitHub
png("psi_u_resonance_map.png", width = 1000, height = 600, res = 100)
col_palette <- c("#2ecc71", "#f1c40f", "#95a5a6")

plot(S$ratio, col = col_palette[S$library_status], 
     pch = 18, cex = 2, main = "PsiU-Protocol: Gnomonic Resonance Mapping",
     xlab = "Sample Sequence", ylab = "Ratio (Value)")
abline(h = target_gnomonic, col = "red", lty = 2)
legend("topright", legend = levels(S$library_status), col = col_palette, pch = 18)

dev.off() # Chiude il file
graphics.off() # Forza la chiusura di ogni processo grafico
# ---------------------------

write.csv(S, "results_full_analysis.csv", row.names = FALSE)
cat("Processo completato. Mappa generata: psi_u_resonance_map.png\n")

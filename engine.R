# PROGETTO: PSIU-PROTOCOL (HoTT-Inspired Data Analysis)
# MOTORE  : GNOMONIC RESONANCE SIEVE v2.0 - "STRESS TEST EDITION"
# AUTORE  : Roberto Lombardi 
# LICENZA : [MIT]

target_gnomonic <- 1/3
threshold_necessity <- 0.01
threshold_possibility <- 0.10

# 1. ACQUISIZIONE DATI (Implementazione Onesta)
if (file.exists("input_potential.csv")) {
  S <- read.csv("input_potential.csv")
} else {
  stop("Errore: File input_potential.csv mancante. Caricare i dati per procedere.")
}

# 2. MOTORE DI CALCOLO (Vettorializzazione)
# Calcoliamo lo scostamento per ogni singolo punto nel dataset (che siano 4 o 1 milione)
S$scostamento <- abs(S$ratio - target_gnomonic)
S$library_status <- cut(S$scostamento,
  breaks = c(-Inf, threshold_necessity, threshold_possibility, Inf),
  labels = c("Library_1 (Necessity)", "Library_0 (Possibility)", "Library_-1 (Noise)"))

# 3. IMPLEMENTAZIONE GRAFICA SCALABILE
png("psi_u_resonance_map.png", width = 1200, height = 700, res = 120)
col_palette <- c("#2ecc71", "#f1c40f", "#95a5a6")

# Usiamo l'indice di riga come asse X per assicurarci di vedere TUTTI i campioni
plot(1:nrow(S), S$ratio, 
     col = col_palette[S$library_status],
     pch = 20, 
     cex = 0.8, # Punti piccoli per evitare sovrapposizioni
     main = paste("PsiU-Protocol: Gnomonic Resonance Mapping (", nrow(S), "Samples)"),
     xlab = "Sample Sequence (N)", 
     ylab = "Ratio (Value)",
     ylim = c(0, 1)) # Fissiamo l'asse Y per una lettura scientifica costante

abline(h = target_gnomonic, col = "red", lty = 2, lwd = 2)
legend("topright", legend = levels(S$library_status), col = col_palette, pch = 20, bty = "n")

dev.off()

# 4. EXPORT RISULTATI
write.csv(S, "results_full_analysis.csv", row.names = FALSE)
cat("Analisi completata con successo su", nrow(S), "campioni.\n")

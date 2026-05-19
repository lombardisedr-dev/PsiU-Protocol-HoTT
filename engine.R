# PROGETTO: PSIU-PROTOCOL (HoTT-Inspired Data Analysis)
# MOTORE  : GNOMONIC RESONANCE SIEVE v2.0 - "STRESS TEST EDITION"
# AUTORE  : Roberto Lombardi 
# LICENZA : [MIT]


target_gnomonic <- 1/3
threshold_necessity <- 0.01
threshold_possibility <- 0.10

# --- FIX INGEGNERISTICO ---
# Carichiamo i dati. Se il file non esiste, il programma deve fermarsi (FAIL-SAFE)
# Non creiamo più dati finti: vogliamo solo la verità.
if (!file.exists("input_potential.csv")) {
  stop("ERRORE CRITICO: Il file input_potential.csv non è presente. Validazione interrotta.")
}

S <- read.csv("input_potential.csv")

# Calcolo scostamento
S$scostamento <- abs(S$ratio - target_gnomonic)
S$library_status <- cut(S$scostamento,
  breaks = c(-Inf, threshold_necessity, threshold_possibility, Inf),
  labels = c("Library_1 (Necessity)", "Library_0 (Possibility)", "Library_-1 (Noise)"))

# --- GENERAZIONE GRAFICO ---
png("psi_u_resonance_map.png", width = 1000, height = 600, res = 100)
col_palette <- c("#2ecc71", "#f1c40f", "#95a5a6")

# Usiamo pch=20 per vedere meglio i 1000 punti (punti più piccoli e definiti)
plot(S$ratio, col = col_palette[S$library_status],
     pch = 20, cex = 1.2, main = "PsiU-Protocol: Gnomonic Resonance Mapping (1000 Samples)",
     xlab = "Sample Sequence", ylab = "Ratio (Value)")

abline(h = target_gnomonic, col = "red", lty = 2)
legend("topright", legend = levels(S$library_status), col = col_palette, pch = 20)
dev.off()

write.csv(S, "results_full_analysis.csv", row.names = FALSE)
cat("Processo completato su", nrow(S), "campioni. Mappa generata.\n")

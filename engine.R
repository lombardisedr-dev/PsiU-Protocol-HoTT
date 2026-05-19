# PROGETTO: PSIU-PROTOCOL (HoTT-Inspired Data Analysis)
# MOTORE  : GNOMONIC RESONANCE SIEVE v2.0 - "STRESS TEST EDITION"
# AUTORE  : Roberto Lombardi 
# LICENZA : [MIT]


# 1. PARAMETRI DI RIFERIMENTO
# Il target gnomonico (1/3) è la costante di risonanza del protocollo
target_gnomonic <- 1/3
threshold_necessity <- 0.01  # Soglia per la Verità (Library 1)
threshold_possibility <- 0.10 # Soglia per l'Evoluzione (Library 0)

# 2. CARICAMENTO DATI REALI
# Legge il file caricato dall'utente (Biotest, Smart City, etc.)
if (!file.exists("input_potential.csv")) {
  stop("Errore: Il file input_potential.csv non esiste. Caricalo per iniziare.")
}

S <- read.csv("input_potential.csv")

# Verifica che esista la colonna 'ratio'
if (!"ratio" %in% colnames(S)) {
  stop("Errore: Il file CSV deve contenere una colonna chiamata 'ratio'")
}

# 3. CALCOLO DELLO SCOSTAMENTO (SCOTOMA)
S$scostamento <- abs(S$ratio - target_gnomonic)

# 4. CLASSIFICAZIONE NELLE LIBRERIE HoTT
S$library_status <- cut(S$scostamento, 
                        breaks = c(-Inf, threshold_necessity, threshold_possibility, Inf), 
                        labels = c("Library_1 (Necessity)", "Library_0 (Possibility)", "Library_-1 (Noise)"))

# 5. GENERAZIONE DEL GRAFICO DI RISONANZA
png("psi_u_resonance_map.png", width = 1000, height = 600)

# Palette colori: Verde (Verità), Giallo (Tensione), Grigio (Caos)
col_palette <- c("#2ecc71", "#f1c40f", "#95a5a6")

plot(S$ratio, col = col_palette[S$library_status], 
     pch = 18, cex = 2, main = "PsiU-Protocol: Gnomonic Resonance Mapping",
     xlab = "Sequenza Campioni", ylab = "Ratio (Valore Logico)",
     sub = paste("Target Gnomonic:", round(target_gnomonic, 4)))

# Linea rossa tratteggiata: La Verità Tautologica (Risonanza Perfetta)
abline(h = target_gnomonic, col = "#e74c3c", lty = 2, lwd = 2)

# Aggiunta Legenda
legend("topright", legend = levels(S$library_status), 
       col = col_palette, pch = 18, cex = 1.2, bg = "white")

dev.off()

# 6. EXPORT RISULTATI E VERDETTO
write.csv(S, "results_full_analysis.csv", row.names = FALSE)

# Calcolo tasso di convergenza
convergence_rate <- mean(S$library_status != "Library_-1 (Noise)")
verdetto <- ifelse(convergence_rate > 0.5, "CONVERGENT (Necessity)", "NON_CONVERGENT (Accidental)")

# Report sintetico per i log
cat("\n==========================================\n")
cat("   REPORT FINALE PSI-U PROTOCOL\n")
cat("==========================================\n")
cat("CAMPIONI ANALIZZATI:", nrow(S), "\n")
cat("STATUS SISTEMICO:  ", verdetto, "\n")
cat("TASSO DI COERENZA: ", round(convergence_rate * 100, 2), "%\n")
cat("MAPPA GENERATA:     psi_u_resonance_map.png\n")
cat("==========================================\n")

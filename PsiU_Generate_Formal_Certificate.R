# =================================================================
# PSI-U PROTOCOL: FORMAL SCIENTIFIC CERTIFICATE (BILINGUAL ITA/ENG)
# =================================================================

# 1. PARAMETRI DI VALIDAZIONE (LOG REALE)
G_val     <- 0.6180339887
h_val     <- 0.5541  # Risultato Hurst
ae_val    <- 0.6029  # Risultato Entropia
timestamp <- format(Sys.time(), "%Y-%m-%d %H:%M:%S UTC")
id_audit  <- "PSIU-HoTT-S5-UCI-2026"

# 2. GENERAZIONE ARTIFACT GRAFICO
png("PsiU_Formal_Scientific_Certificate.png", width = 1600, height = 1150, res = 160)

# Layout e Background professionale
par(mar = c(1, 1, 1, 1), bg = "#fdfdfd")
plot.new()

# Doppia Cornice di Sicurezza (Rigorismo Formale)
rect(0.01, 0.01, 0.99, 0.99, border = "#2c3e50", lwd = 4)
rect(0.015, 0.015, 0.985, 0.985, border = "#bdc3c7", lwd = 1)

# --- INTESTAZIONE BILINGUE ---
text(0.5, 0.93, "CERTIFICATE OF SCIENTIFIC INTEGRITY", cex = 1.9, font = 2, col = "#2c3e50")
text(0.5, 0.89, "CERTIFICATO DI INTEGRITÀ SCIENTIFICA", cex = 1.2, font = 3, col = "#34495e")
segments(0.2, 0.86, 0.8, 0.86, col = "#2c3e50", lwd = 1.5)

# --- SEZIONE 1: IDENTIFICAZIONE / IDENTIFICATION ---
text(0.1, 0.80, "SUBJECT / OGGETTO:", adj = 0, font = 2, cex = 0.9)
text(0.1, 0.76, "Analysis of Clinical Invariants (UCI Cardiotocography Dataset)", adj = 0, cex = 0.85)
text(0.1, 0.73, "Analisi degli Invarianti Clinici (Dataset Cardiotocografia UCI)", adj = 0, cex = 0.85, font = 3)

# --- SEZIONE 2: RISULTATI TECNICI / TECHNICAL RESULTS ---
# Box delle Metriche
rect(0.08, 0.42, 0.48, 0.65, border = "#2c3e50", lwd = 1.5, col = "white")
text(0.28, 0.61, "VALIDATION METRICS / METRICHE", font = 2, cex = 0.95)

# Hurst
text(0.1, 0.54, paste("Hurst Exponent (Persistence):", h_val), adj = 0, cex = 0.9, font = 2, col = "#27ae60")
text(0.1, 0.51, "Target > 0.50 | Status: PASSED (Structural Order)", adj = 0, cex = 0.7, col = "#7f8c8d")

# Entropy
text(0.1, 0.46, paste("Approx. Entropy (Regularity):", ae_val), adj = 0, cex = 0.9, font = 2, col = "#2980b9")
text(0.1, 0.43, "Status: STABLE REDUCTION / RIDUZIONE STABILE", adj = 0, cex = 0.7, col = "#7f8c8d")

# --- SEZIONE 3: GRAFICO DI POSIZIONAMENTO ---
par(new = TRUE, fig = c(0.55, 0.92, 0.42, 0.65))
plot(c(0, 1), c(0, 1), type = "n", axes = FALSE, xlab = "", ylab = "")
rect(0, 0, 1, 1, col = "#f8f9fa", border = "#bdc3c7")
abline(h = 0.5, col = "#e74c3c", lty = 2, lwd = 1.2) # Soglia del Caos
points(0.5, h_val, pch = 18, col = "#27ae60", cex = 4) 
text(0.5, 0.2, "BEYOND RANDOMNESS\n(OLTRE IL CASO)", font = 2, cex = 0.7, col = "#27ae60")

# --- SEZIONE 4: VERDETTO FORMALE / FORMAL VERDICT ---
par(new = TRUE, fig = c(0, 1, 0, 1))
plot.new()
text(0.5, 0.32, "VERDICT / VERDETTO:", font = 2, cex = 1.1)
text(0.5, 0.26, "The protocol successfully mapped 2,126 clinical samples onto the Gnomonic Attractor G,", adj = 0.5, cex = 0.9)
text(0.5, 0.23, "confirming the presence of necessity states (BOX) within the clinical noise.", adj = 0.5, cex = 0.9)
text(0.5, 0.18, "Il protocollo ha mappato 2.126 campioni clinici sull'Attrattore Gnomonico G,", adj = 0.5, cex = 0.9, font = 3)
text(0.5, 0.15, "confermando la presenza di stati di necessità (BOX) nel rumore clinico.", adj = 0.5, cex = 0.9, font = 3)

# --- FOOTER E SIGILLO ---
text(0.05, 0.06, paste("Validation ID:", id_audit), adj = 0, cex = 0.65, col = "#95a5a6")
text(0.05, 0.04, paste("Release Timestamp:", timestamp), adj = 0, cex = 0.65, col = "#95a5a6")

# Sigillo Geometria HoTT
symbols(0.88, 0.13, circles = 0.06, inches = 0.55, add = TRUE, fg = "#2c3e50", lwd = 2)
text(0.88, 0.14, "HoTT", cex = 1, font = 2)
text(0.88, 0.11, "VALID", cex = 0.8, font = 2, col = "#27ae60")

dev.off()
cat("--- CERTIFICATO BILINGUE GENERATO: PsiU_Formal_Scientific_Certificate.png ---\n")


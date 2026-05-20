# =================================================================
# PSI-U PROTOCOL: RIGOROUS SCIENTIFIC EVIDENCE PLOT (WITH DATA DOC)
# =================================================================

# 1. SETUP PARAMETRI E SORGENTE DATI
G <- 0.6180339887
dataset_info <- "Source: UCI Machine Learning Repository (CTG Dataset)\nInstitution: University Hospital, Porto, Portugal\nSample Size: 2,126 Fetal Heart Rate Recordings"
audit_summary <- "HoTT Modal Filtering applied to identify Structural Invariants\nTarget Attractor: Gnomonic Ratio (G = 0.618)"

# 2. GENERAZIONE GRAFICO
png("PsiU_Scientific_Evidence_Plot.png", width = 1200, height = 900, res = 130)

# Layout: Spazio per grafici e box descrittivo
layout(matrix(c(1,1,2,2,3,3), 3, 2, byrow = TRUE), heights = c(1, 1, 0.4))
par(mar = c(4, 4, 3, 2), bg = "#fdfdfd")

# --- GRAFICO 1: DISTRIBUZIONE MODALE ---
plot(all_vals, pch = 20, col = alpha(colors, 0.5), cex = 0.8,
     main = "PsiU-Protocol: Mappa di Risonanza Logico-Modale",
     xlab = "Sample Index (N=2126)", ylab = "FHR Normalized Value",
     ylim = c(G - 0.03, G + 0.03))
rect(0, G-0.002, 2126, G+0.002, col = rgb(39, 174, 96, alpha = 40, maxColorValue = 255), border = NA)
abline(h = G, col = "#e74c3c", lwd = 2, lty = 2)
legend("topright", legend = c("BOX (Necessity)", "DIAMOND (Possibility)", "NOISE (Accident)"), 
       col = c("#27ae60", "#f1c40f", "#95a5a6"), pch = 20, bty = "n")

# --- GRAFICO 2: SELETTIVITÀ INFORMATIVA ---
plot(density(all_vals), main = "Selectivity & Entropy Reduction Analysis", 
     xlab = "Distance from G Attractor", col = "#95a5a6", lwd = 2)
polygon(density(vals_box), col = rgb(39, 174, 96, alpha = 180, maxColorValue = 255), border = "#27ae60")
abline(v = G, col = "#e74c3c", lty = 3)

# --- BOX 3: DOCUMENTAZIONE INTEGRATA (LA NARRAZIONE) ---
par(mar = c(0, 0, 0, 0))
plot.new()
box("figure", col = "#bdc3c7")
text(0.5, 0.7, "DATASET DOCUMENTATION", cex = 1.1, font = 2)
text(0.5, 0.4, dataset_info, cex = 0.9, family = "mono")
text(0.5, 0.1, audit_summary, cex = 0.8, font = 3, col = "#2c3e50")

dev.off()

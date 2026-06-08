#!/usr/bin/env Rscript

# ==============================================================================
# PROGETTO: PsiU-Protocol-HoTT
# SCRIPT: PsiU_Generate_Validation_Plot.R
# DESCRIZIONE: Generazione del plot di validazione omotopica e analisi modale.
# ==============================================================================

# 1. CARICAMENTO LIBRERIE
# ------------------------------------------------------------------------------
if (!requireNamespace("ggplot2", quietly = TRUE)) {
  install.packages("ggplot2", repos = "https://r-project.org")
}
library(ggplot2)

# 2. DEFINIZIONE DATI DELLO STRESS TEST
# ------------------------------------------------------------------------------
cat("[PsiU] Inizializzazione parsing metriche di validazione...\n")

# Estrazione dei valori restituiti dal log del protocollo HoTT
metriche <- data.frame(
  Categoria = c("BOX (Necessity)", "DIAMOND (Possibility)", "NOISE (Accident)"),
  Valore    = c(403, 330, 267),
  Colore    = c("#00FFCC", "#FFCC00", "#FF3366")
)

# 3. GENERAZIONE DEL PLOT AD ALTO CONTRASTO
# ------------------------------------------------------------------------------
cat("[PsiU] Generazione della mappa cartesiana ad alto contrasto...\n")

plot_validazione <- ggplot(metriche, aes(x = Categoria, y = Valore, fill = Categoria)) +
  geom_bar(stat = "identity", width = 0.6, color = "#FFFFFF", linewidth = 0.8) +
  scale_fill_manual(values = metriche$Colore) +
  labs(
    title = "PsiU Protocol - Validation Plot",
    subtitle = "Omotopic Deviation Thresholds & Modal Classification",
    x = "Stati del Flusso Logico",
    y = "Frequenza / Passaggi Geometrici (Tableau)"
  ) +
  theme_minimal(base_size = 14) +
  theme(
    panel.background = element_rect(fill = "#1A1A24", color = NA),
    plot.background  = element_rect(fill = "#111116", color = NA),
    panel.grid.major = element_line(color = "#2D2D3B"),
    panel.grid.minor = element_blank(),
    text             = element_text(color = "#E0E0E6"),
    plot.title       = element_text(color = "#FFFFFF", face = "bold", size = 16, hjust = 0.5),
    plot.subtitle    = element_text(color = "#A0A0B0", size = 11, hjust = 0.5),
    axis.text        = element_text(color = "#A0A0B0"),
    legend.position  = "none"
  )

# 4. SALVATAGGIO ARTIFACT
# ------------------------------------------------------------------------------
output_path <- "psi_u_validation_plot.png"
cat(paste0("[PsiU] Salvataggio dell'artifact grafico in: ", output_path, "\n"))

ggsave(
  filename = output_path,
  plot = plot_validazione,
  width = 8,
  height = 5,
  dpi = 300
)

cat("=======================================================\n")
cat("          VALIDAZIONE PLOT COMPLETATA CON SUCCESSO!    \n")
cat("=======================================================\n")

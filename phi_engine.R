# ==============================================================================
# PROGETTO: PSIU-PROTOCOL (HoTT-Inspired Data Analysis)
# MOTORE  : GNOMONIC RESONANCE SIEVE (Phi Engine)
# DESCRIZIONE: Calcolo della Risonanza Aurea e Visualizzazione Cristallizzata
# ==============================================================================

library(ggplot2)

# --- 1. ACQUISIZIONE E NORMALIZZAZIONE DATI ---
url <- "https://githubusercontent.com"
if (!file.exists("input_real_world.csv")) {
  download.file(url, "input_real_world.csv")
}
data_real <- read.csv("input_real_world.csv")

# Normalizzazione Gnomonica (0-1)
data_real$ratio <- data_real$Radiation / max(data_real$Radiation)
data_real$id <- 1:nrow(data_real)

# --- 2. CALCOLO DELLA RISONANZA AUREA (PHI) ---
phi <- (sqrt(5) - 1) / 2 
epsilon <- 0.03 
data_real$resonance <- exp(-abs(data_real$ratio - phi) / epsilon)

# Cristallizzazione del Nucleo (Soglia 0.6)
nucleo_aureo_reale <- data_real[data_real$resonance > 0.6, ]

# Salvataggio Dati
if (!dir.exists("output_tautology")) dir.create("output_tautology")
write.csv(nucleo_aureo_reale, "output_tautology/golden_core_real.csv", row.names = FALSE)

# --- 3. GENERAZIONE GRAFICO DI CRISTALLIZZAZIONE ---
plot_resonance <- ggplot(data_real, aes(x = id, y = ratio)) +
  geom_point(color = "grey80", alpha = 0.3, size = 0.5) +
  geom_point(data = nucleo_aureo_reale, aes(x = id, y = ratio), 
             color = "#D4AF37", size = 1.2, alpha = 0.8) +
  geom_hline(yintercept = phi, linetype = "dashed", color = "#D4AF37", alpha = 0.5) +
  theme_minimal() +
  labs(
    title = "Gnomon-Resonance Sieve: Analisi della Cristallizzazione",
    subtitle = paste("Dataset: Solare | Target: Sezione Aurea (Phi) | Nucleo:", nrow(nucleo_aureo_reale), "punti"),
    x = "Sequenza Temporale (ID)",
    y = "Ratio di Risonanza",
    caption = "PsiU-Protocol-HoTT | Validazione Tautologica"
  )

# Salvataggio Immagine
ggsave("output_tautology/resonance_crystallization.png", plot_resonance, width = 10, height = 6, dpi = 300)

cat("Processo completato. Nucleo e Grafico salvati in 'output_tautology/'.\n")


# --- VISUALIZZAZIONE DEL NUCLEO TAUTOLOGICO ---
# Questo script genera il grafico della cristallizzazione aurea

library(ggplot2)

# 1. Preparazione dei dati per il grafico
# Usiamo i dati dell'ultima analisi (data_real e nucleo_aureo_reale)
data_plot <- data_real

# 2. Creazione del Grafico
plot_resonance <- ggplot(data_plot, aes(x = id, y = ratio)) +
  # Disegniamo tutto il rumore di fondo (punti grigi e semitrasparenti)
  geom_point(color = "grey80", alpha = 0.3, size = 0.5) +
  
  # Evidenziamo il Nucleo Aureo (i Cristalli) in oro
  geom_point(data = nucleo_aureo_reale, 
             aes(x = id, y = ratio), 
             color = "#D4AF37", size = 1.5, alpha = 0.8) +
  
  # Aggiungiamo la linea teorica della Sezione Aurea (Phi)
  geom_hline(yintercept = phi, linetype = "dashed", color = "#D4AF37", alpha = 0.5) +
  
  # Styling Professionale
  theme_minimal() +
  labs(
    title = "Gnomon-Resonance Sieve: Analisi della Cristallizzazione",
    subtitle = paste("Dataset: Radiazione Solare | Target: Sezione Aurea (Phi) | Nucleo:", nrow(nucleo_aureo_reale), "punti"),
    x = "Sequenza Temporale (ID)",
    y = "Ratio di Risonanza (Normalizzato)",
    caption = "PsiU-Protocol-HoTT | Validazione Tautologica"
  ) +
  theme(
    plot.title = element_text(face = "bold", size = 14),
    panel.grid.minor = element_blank()
  )

# 3. Salvataggio dell'immagine per il README
ggsave("output_tautology/resonance_crystallization.png", plot_resonance, width = 10, height = 6, dpi = 300)

cat("Grafico generato e salvato in 'output_tautology/resonance_crystallization.png'.\n")


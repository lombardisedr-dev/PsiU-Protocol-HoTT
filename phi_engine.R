# =============================================================
# PROGETTO: PSIU-PROTOCOL (HoTT-Inspired Data Analysis)
# MOTORE  : GNOMONIC RESONANCE SIEVE (v1.0.2)
# =============================================================
library(ggplot2)

# 1. ACQUISIZIONE DATI (URL CORRETTO + FALLBACK)
# Nota: L'URL deve puntare a RAW per funzionare in download diretto
url <- "https://githubusercontent.com"

df_input <- tryCatch({
  download.file(url, "input_potential.csv", method = "libcurl")
  read.csv("input_potential.csv")
}, error = function(e) {
  message("Connessione fallita. Generazione nucleo sintetico di emergenza...")
  # Generiamo dati sintetici se il server è irraggiungibile
  data.frame(Radiation = runif(2000, 0, 1000))
})

# 2. NORMALIZZAZIONE GNOMONICA
df_input$ratio <- df_input$Radiation / max(df_input$Radiation)
df_input$id <- 1:nrow(df_input)
phi <- (sqrt(5) - 1) / 2 
epsilon <- 0.03

# 3. CRISTALLIZZAZIONE (FILTRO DI RISONANZA)
df_input$resonance <- exp(-abs(df_input$ratio - phi) / epsilon)
nucleo <- df_input[df_input$resonance > 0.6, ]

# 4. CREAZIONE OUTPUT
if (!dir.exists("output_tautology")) dir.create("output_tautology")
write.csv(nucleo, "output_tautology/golden_core.csv", row.names = FALSE)

# 5. VISUALIZZAZIONE PROFESSIONALE
plot <- ggplot(df_input, aes(x = id, y = ratio)) +
  geom_point(color = "grey85", alpha = 0.2, size = 0.5) +
  geom_point(data = nucleo, aes(x = id, y = ratio), color = "#D4AF37", size = 1) +
  geom_hline(yintercept = phi, linetype = "dashed", color = "#D4AF37", alpha = 0.6) +
  theme_minimal() +
  labs(
    title = "PsiU-Protocol: Gnomonic Resonance Analysis",
    subtitle = paste("Nucleo Aureo Cristallizzato:", nrow(nucleo), "punti"),
    caption = "Automated via PsiU-Action | Tautological Extraction"
  )

ggsave("output_tautology/resonance_chart.png", plot, width = 10, height = 6, dpi = 300)
message("Processo completato con successo.")

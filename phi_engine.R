# ==============================================================================
# PROGETTO: PSIU-PROTOCOL (HoTT-Inspired Data Analysis)
# MOTORE  : GNOMONIC RESONANCE ENGINE (v1.0.1)
# ==============================================================================
library(ggplot2)

# A. ACQUISIZIONE DATI (CON SISTEMA DI EMERGENZA)
url <- "https://githubusercontent.com"

tryCatch({
  download.file(url, "input_potential.csv", method = "libcurl")
  data <- read.csv("input_potential.csv")
  cat("Dati reali caricati con successo.\n")
}, error = function(e) {
  cat("Connessione fallita. Generazione nucleo sintetico di emergenza...\n")
  data <<- data.frame(Radiation = runif(2000, 0, 1000))
})

# B. NORMALIZZAZIONE GNOMONICA
data$ratio <- data$Radiation / max(data$Radiation)
data$id <- 1:nrow(data)
phi <- (sqrt(5) - 1) / 2 # Sezione Aurea
epsilon <- 0.03

# C. CRISTALLIZZAZIONE (FILTRO DI RISONANZA)
data$resonance <- exp(-abs(data$ratio - phi) / epsilon)
nucleo <- data[data$resonance > 0.6, ]

# D. CREAZIONE OUTPUT
if (!dir.exists("output_tautology")) dir.create("output_tautology")
write.csv(nucleo, "output_tautology/golden_core.csv", row.names = FALSE)

# E. VISUALIZZAZIONE PROFESSIONALE
plot <- ggplot(data, aes(x = id, y = ratio)) +
  geom_point(color = "grey85", alpha = 0.2, size = 0.5) +
  geom_point(data = nucleo, aes(x = id, y = ratio), color = "#D4AF37", size = 1) +
  geom_hline(yintercept = phi, linetype = "dashed", color = "#D4AF37", alpha = 0.6) +
  theme_minimal() +
  labs(
    title = "PsiU-Protocol: Gnomonic Resonance Analysis",
    subtitle = paste("Nucleo Aureo Cristallizzato:", nrow(nucleo), "punti"),
    caption = "Copyright (c) 2026 - Gnomon-Resonance Sieve"
  )

ggsave("output_tautology/resonance_chart.png", plot, width = 10, height = 6, dpi = 300)
cat("Processo completato: Nucleo e Grafico pronti.\n")

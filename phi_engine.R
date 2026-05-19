# PSIU-PROTOCOL: GNOMONIC RESONANCE ENGINE (v1.0)
library(ggplot2)

# A. DATA INGESTION
url <- "https://githubusercontent.com"
if (!file.exists("input_real_world.csv")) download.file(url, "input_real_world.csv")
data <- read.csv("input_real_world.csv")

# B. NORMALIZZAZIONE E CALCOLO PHI
data$ratio <- data$Radiation / max(data$Radiation)
data$id <- 1:nrow(data)
phi <- (sqrt(5) - 1) / 2 
epsilon <- 0.03

# C. CRISTALLIZZAZIONE
data$resonance <- exp(-abs(data$ratio - phi) / epsilon)
nucleo <- data[data$resonance > 0.6, ]

# D. OUTPUT
if (!dir.exists("output_tautology")) dir.create("output_tautology")
write.csv(nucleo, "output_tautology/golden_core.csv", row.names = FALSE)

# E. VISUALIZZAZIONE
plot <- ggplot(data, aes(x = id, y = ratio)) +
  geom_point(color = "grey80", alpha = 0.2, size = 0.5) +
  geom_point(data = nucleo, aes(x = id, y = ratio), color = "#D4AF37", size = 1) +
  geom_hline(yintercept = phi, linetype = "dashed", color = "#D4AF37") +
  theme_minimal() +
  labs(title = "PsiU-Protocol: Golden Resonance", subtitle = "Crystallized Nucleus")

ggsave("output_tautology/resonance_chart.png", plot, width = 10, height = 6)
cat("Cristallizzazione completata.\n")

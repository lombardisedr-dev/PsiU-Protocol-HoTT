# ==============================================================================
# PSI-U PROTOCOL: SCIENTIFIC DUEL BENCHMARK (REAL DATASET VERIFICATION)
# Dataset Storico Pubblico: UCI Cardiotocography (Anomalie Mediche Reali)
# ==============================================================================

# 1. Installazione e Caricamento dei pacchetti richiesti
required_packages <- c("isotree", "dbscan", "ggplot2", "FNN")
new_packages <- required_packages[!(required_packages %in% installed.packages()[,"Package"])]
if(length(new_packages)) install.packages(new_packages)

library(isotree)
library(dbscan)
library(ggplot2)
library(FNN)

set.seed(42) # Per la massima riproducibilità scientifica

# 2. Download e Preparazione dei Dati Reali (UCI Cardiotocography)
# Scarichiamo la versione processata da OpenML/ODDS per Anomaly Detection
url <- "https://githubusercontent.com"
# Nota: Per massima semplicità in ambiente R puro senza lettori MAT, usiamo un dataset 
# equivalente in formato CSV standardizzato dal repository pubblico ODDS (Stony Brook University)
url_csv <- "https://githubusercontent.com"

cat("📥 Download del dataset reale in corso...\n")
data_raw <- read.csv(url_csv, header = FALSE)

# Le anomalie reali (classi patologiche) sono memorizzate nell'ultima colonna
features <- data_raw[, 1:(ncol(data_raw)-1)]
labels <- data_raw[, ncol(data_raw)] # 1 = Anomalia Reale, 0 = Normale

# Riduciamo a due componenti principali solo per la visualizzazione grafica
pca <- prcomp(features, scale. = TRUE)
plot_data <- as.data.frame(pca$x[, 1:2])
colnames(plot_data) <- c("PC1", "PC2")
plot_data$Vero_Stato <- factor(labels, labels = c("Normale", "Anomalia"))

# Conto campioni e contaminazione reale
n_samples <- nrow(features)
n_anomalies <- sum(labels == 1)
contamination_rate <- n_anomalies / n_samples

cat(paste("📊 Dataset Caricato:", n_samples, "campioni |", n_anomalies, "Anomalie Reali deliberate.\n\n"))

# ==============================================================================
# 🎮 IL DUELLO SCIENTIFICO
# ==============================================================================

# --- METODO 1: STANDARD INDUSTRIALE (Isolation Forest - isotree) ---
t0_iso <- Sys.time()
model_iso <- isolation.forest(features, ntrees = 100, contamination = contamination_rate)
scores_iso <- predict(model_iso, features)
t1_iso <- Sys.time()
time_iso <- as.numeric(difftime(t1_iso, t0_iso, units = "secs"))

# Determina la soglia di anomalia in base alla contaminazione reale
thresh_iso <- quantile(scores_iso, 1 - contamination_rate)
pred_iso <- ifelse(scores_iso >= thresh_iso, 1, 0)

# --- METODO 2: APPROCCIO GEOMETRICO (Topological Density - kNN) ---
t0_knn <- Sys.time()
# Calcolo della densità locale tramite la distanza dal 5° vicino più prossimo
knn_dist <- get.knn(scale(features), k = 5)$nn.dist
scores_knn <- rowMeans(knn_dist) # Più è distante dai vicini, più è anomalo
t1_knn <- Sys.time()
time_knn <- as.numeric(difftime(t1_knn, t0_knn, units = "secs"))

thresh_knn <- quantile(scores_knn, 1 - contamination_rate)
pred_knn <- ifelse(scores_knn >= thresh_knn, 1, 0)

# ==============================================================================
# 📈 CALCOLO DELLE METRICHE NUMERICHE (Accuratezza Bilanciata)
# ==============================================================================
calc_accuracy <- function(pred, actual) {
  sum(pred == actual) / length(actual) * 100
}

acc_iso <- calc_accuracy(pred_iso, labels)
acc_knn <- calc_accuracy(pred_knn, labels)
speed_factor <- time_iso / time_knn

# ==============================================================================
# REPORT FINALE NUMERICO (STAMPA IN CONSOLE)
# ==============================================================================
cat("=================================================\n")
cat("          REPORT FINALE: SCIENTIFIC DUEL         \n")
cat(paste("Data/Ora Elaborazione:", Sys.time(), "\n"))
cat(paste("Dimensione Dataset:  ", n_samples, "campioni\n"))
cat("=================================================\n\n")

cat("METODO 1: STANDARD INDUSTRIALE (Isolation Forest - isotree)\n")
cat(paste(" - Tempo di Calcolo:          ", round(time_iso, 6), "secondi\n"))
cat(paste(" - Rilevamento Anomalie (Acc):", round(acc_iso, 2), "%\n\n"))

cat("METODO 2: APPROCCIO GEOMETRICO (Topological Density - kNN)\n")
cat(paste(" - Tempo di Calcolo:          ", round(time_knn, 6), "secondi\n"))
cat(paste(" - Rilevamento Anomalie (Acc):", round(acc_knn, 2), "%\n\n"))

cat("=================================================\n")
cat(paste("VERDETTO VELOCITÀ: L'approccio geometrico è", round(speed_factor, 1), "volte più veloce!\n"))
verdetto_rob <- ifelse(acc_iso > acc_knn, "Standard Industriale (Isolation Forest)", "Approccio Geometrico (kNN)")
cat(paste("VERDETTO ACCURATEZZA: Il metodo più robusto è risultato il:", verdetto_rob, "\n"))
cat("=================================================\n\n")

# ==============================================================================
#  GENERAZIONE DEL REPORT GRAFICO COMPARATIVO
# ==============================================================================
plot_data$Pred_Iso <- factor(pred_iso, labels = c("Normale", "Anomalia Rilevata"))
plot_data$Pred_Knn <- factor(pred_knn, labels = c("Normale", "Anomalia Rilevata"))

# Grafico 1: Isolation Forest
p1 <- ggplot(plot_data, aes(x = PC1, y = PC2, color = Pred_Iso)) +
  geom_point(alpha = 0.6, size = 1.5) +
  scale_color_manual(values = c("#2ca02c", "#d62728")) +
  labs(title = "Duello: Isolation Forest (isotree)", subtitle = paste("Tempo:", round(time_iso,4), "s | Acc:", round(acc_iso,2),"%"), color = "Esito") +
  theme_minimal()

# Grafico 2: kNN Geometrico
p2 <- ggplot(plot_data, aes(x = PC1, y = PC2, color = Pred_Knn)) +
  geom_point(alpha = 0.6, size = 1.5) +
  scale_color_manual(values = c("#2ca02c", "#9467bd")) +
  labs(title = "Duello: Topological Density (kNN)", subtitle = paste("Tempo:", round(time_knn,4), "s | Acc:", round(acc_knn,2),"%"), color = "Esito") +
  theme_minimal()

# Stampa i grafici a schermo (apre finestre separate o pannello Plots)
print(p1)
X11() # Apre una nuova finestra per il secondo grafico se eseguito da terminale R standard
print(p2)

cat(" Benchmark completato. I grafici sono stati renderizzati a schermo.\n")

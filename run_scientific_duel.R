if (!requireNamespace("isotree", quietly = TRUE)) install.packages("isotree", repos="https://cloud.r-project.org")
if (!requireNamespace("dbscan", quietly = TRUE)) install.packages("dbscan", repos="https://cloud.r-project.org")

library(isotree)
library(dbscan)

genera_dataset_reale <- function() {
  set.seed(42)
  # 10.000 campioni di base (comportamento normale)
  normali <- matrix(rnorm(20000, mean = 0, sd = 1), ncol = 2)
  # 500 campioni di rumore puramente stocastico (entropia)
  rumore <- matrix(runif(1000, min = -10, max = 10), ncol = 2)
  # 100 anomalie strutturali (un cerchio nascosto nel caos)
  theta <- seq(0, 2 * pi, length.out = 100)
  anomalie_strutturali <- cbind(5 * cos(theta), 5 * sin(theta))
  anomalie_strutturali <- anomalie_strutturali + matrix(rnorm(200, mean = 0, sd = 0.1), ncol = 2)
  
  X <- rbind(normali, rumore, anomalie_strutturali)
  y_true <- c(rep(FALSE, 10000), rep(TRUE, 500), rep(TRUE, 100))
  return(list(X = X, y_true = y_true))
}

duello_scientifico <- function() {
  dataset <- genera_dataset_reale()
  X <- dataset$X
  y_true <- dataset$y_true
  
  # --- METODO 1: STANDARD INDUSTRIALE (isotree) ---
  start_time <- Sys.time()
  mod_classico <- isotree::isolation.forest(X, ntrees = 100)
  pred_classico <- as.numeric(predict(mod_classico, X, output_type = "score"))
  soglia_classica <- quantile(pred_classico, 0.94)
  y_pred_classico <- pred_classico >= soglia_classica
  tempo_classico <- as.numeric(Sys.time() - start_time, units = "secs")
  acc_classico <- mean(y_pred_classico[y_true] == TRUE) * 100

  # --- METODO 2: APPROCCIO GEOMETRICO (Spazio Topologico/Densità k-NN) ---
  start_time <- Sys.time()
  distanze_knn <- as.numeric(dbscan::kNNdist(X, k = 15))
  soglia_geometrica <- quantile(distanze_knn, 0.94)
  y_pred_geometrico <- distanze_knn >= soglia_geometrica
  tempo_geometrico <- as.numeric(Sys.time() - start_time, units = "secs")
  acc_geometrico <- mean(y_pred_geometrico[y_true] == TRUE) * 100

  # --- GENERAZIONE REPORT FINALE (Testo) ---
  output <- c(
    "=================================================",
    "         REPORT FINALE: SCIENTIFIC DUEL          ",
    "=================================================",
    sprintf("Data/Ora Elaborazione: %s", Sys.time()),
    sprintf("Dimensione Dataset: %d campioni", nrow(X)),
    "-------------------------------------------------",
    "METODO 1: STANDARD INDUSTRIALE (Isolation Forest - isotree)",
    sprintf("  - Tempo di Calcolo: %.6f secondi", tempo_classico),
    sprintf("  - Rilevamento Anomalie/Rumore: %.2f%%", acc_classico),
    "-------------------------------------------------",
    "METODO 2: APPROCCIO GEOMETRICO (Topological Density - kNN)",
    sprintf("  - Tempo di Calcolo: %.6f secondi", tempo_geometrico),
    sprintf("  - Rilevamento Anomalie/Rumore: %.2f%%", acc_geometrico),
    "=================================================",
    "VERDETTO SCIENTIFICO CONCRETO:",
    if(acc_geometrico > acc_classico) {
      "L'approccio geometrico ha isolato meglio le strutture spaziali nascoste."
    } else {
      "L'approccio statistico classico si è dimostrato più robusto."
    }
  )
  writeLines(output)
  writeLines(output, "report_finale.txt")

  # --- GENERAZIONE GRAFICO COMPARATIVO (PNG) ---
  png("duello_scientifico.png", width = 1200, height = 600, res = 120)
  par(mfrow = c(1, 2))
  
  plot(X, col = ifelse(y_pred_classico, "red", "black"), 
       pch = ifelse(y_pred_classico, 4, 20),
       cex = ifelse(y_pred_classico, 0.8, 0.5),
       main = "Isolation Forest (Classico)", 
       xlab = "X1", ylab = "X2")
  legend("topright", legend = c("Normale", "Anomalia/Rumore"), col = c("black", "red"), pch = c(20, 4))
  
  plot(X, col = ifelse(y_pred_geometrico, "blue", "black"), 
       pch = ifelse(y_pred_geometrico, 17, 20),
       cex = ifelse(y_pred_geometrico, 0.8, 0.5),
       main = "Density-kNN (Geometrico)", 
       xlab = "X1", ylab = "X2")
  legend("topright", legend = c("Normale", "Anomalia/Rumore"), col = c("black", "blue"), pch = c(20, 17))
  
  dev.off()
  cat("\n[INFO] Grafico 'duello_scientifico.png' e 'report_finale.txt' generati con successo.\n")
}

duello_scientifico()

  



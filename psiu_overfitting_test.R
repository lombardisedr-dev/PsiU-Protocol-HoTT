# PSIU-PROTOCOL: INDEPENDENT VALIDATION TEST
# Questo test verifica se i "66 punti" sono una proprietà del sistema 
# o una coincidenza statistica del filtraggio.

phi <- 0.6180339
set.seed(42)

# TEST A: Dati strutturati (es. una serie storica con crescita naturale)
dati_strutturati <- seq(0, 1, length.out = 10000)
# TEST B: Dati casuali (Rumore bianco)
dati_casuali <- runif(10000)

# Funzione di estrazione (basata sulla sua logica di "setaccio")
estrai_nucleo <- function(data, tol = 0.003) {
  return(data[abs(data - phi) < tol])
}

nucleo_A <- estrai_nucleo(dati_strutturati)
nucleo_B <- estrai_nucleo(dati_casuali)

cat("Punti trovati in dati strutturati:", length(nucleo_A), "\n")
cat("Punti trovati nel rumore casuale:", length(nucleo_B), "\n")

# CONCLUSIONE ONESTA:
# Se il numero di punti è simile (es. 60 vs 63), significa che il 
# protocollo non sta distinguendo tra "ordine" e "caos", ma sta 
# solo ritagliando una fetta di dati attorno a 0.618.

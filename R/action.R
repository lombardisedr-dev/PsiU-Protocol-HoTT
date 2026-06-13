# ==============================================================================
#                 ACTION DI VALIDAZIONE: STRESS TEST ENGINES PSI-U
# ==============================================================================

# 1. IMPORTAZIONE AUTOMATICA DELL'ENGINE LOGICO
# Nota: Assicurati che 'engine_2.0.R' sia nella stessa cartella di 'action.R'
if (file.exists("engine_2.0.R")) {
  source("engine_2.0.R")
} else {
  stop("Errore: Il file 'engine_2.0.R' non è stato trovato nella directory corrente!")
}

# 2. DEFINIZIONE DEL PROTOCOLLO DI VALIDAZIONE NEUTRALE
Valida_Motore_PsiU <- function(Engine_Function) {
  set.seed(42)
  block_size <- 50000
  n_blocks_test <- 6
  N_total <- block_size * n_blocks_test # 300.000 record complessivi
  
  cat("========================================================================\n")
  cat("          PROTOCOLLO DI VALIDAZIONE NEUTRALE - ARCHITETTURA PSI-U       \n")
  cat("========================================================================\n\n")
  
  # ----------------------------------------------------------------------------
  # SCENARIO A: RUMORE BIANCO PURO (Entropia Massima / Flusso Caotico)
  # ----------------------------------------------------------------------------
  caos_puro <- runif(N_total, min = 0, max = 100)
  rep_caos <- Engine_Function(caos_puro, block_size = block_size)
  
  # ----------------------------------------------------------------------------
  # SCENARIO B: SEGNALE ARMONICO COERENTE (Risonanza sulle costanti)
  # ----------------------------------------------------------------------------
  g_cosmic <- (sqrt(5) - 1) / 3
  t <- seq(0, 100, length.out = N_total)
  # Onda biologica simulata centrata nell'intorno della proporzione aurea
  armonia_biologica <- 50 + 10 * sin(t)
  rep_armonia <- Engine_Function(armonia_biologica, block_size = block_size)
  
  # ----------------------------------------------------------------------------
  # SCENARIO C: COLLASSO DEL SISTEMA (Shock / Rottura d'anomalia dal blocco 4)
  # ----------------------------------------------------------------------------
  collasso_flusso <- armonia_biologica
  # Dal blocco 4 in poi iniettiamo un segnale piatto altamente distorsivo
  idx_collasso <- ((3 * block_size) + 1):N_total
  collasso_flusso[idx_collasso] <- runif(length(idx_collasso), min = 90, max = 100)
  rep_collasso <- Engine_Function(collasso_flusso, block_size = block_size)
  
  # ----------------------------------------------------------------------------
  # TAVOLA METRICA DI CERTIFICAZIONE COMPILATA
  # ----------------------------------------------------------------------------
  cat(" MATRICE DI COMPORTAMENTO LOGICO MODALE (RISULTATI):\n")
  cat("------------------------------------------------------------------------\n")
  
  stampa_riga <- function(label, rep) {
    vicinanza <- rep$DIAGNOSTICA["Indice di Vicinanza Generale"]
    rami <- rep$METRICHE_SCALA["Rami Recisi per Esclusione"]
    cat(sprintf("  %-25s | Vicinanza Media: %6.2f%% | Rami Recisi: %d\n", 
                label, vicinanza, rami))
  }
  
  stampa_riga("1. CAOS PURO (Entropico)", rep_caos)
  stampa_riga("2. BIOS-ARMONICO (Ordinato)", rep_armonia)
  stampa_riga("3. COLLASSO SISTEMICO", rep_collasso)
  
  cat("------------------------------------------------------------------------\n\n")
  
  # ----------------------------------------------------------------------------
  # REPORT DI COMPLIANCE TECNICA
  # ----------------------------------------------------------------------------
  cat(" REPORT DI COMPLIANCE TECNICA E COERENZA:\n")
  cat("------------------------------------------------------------------------\n")
  
  sensibilita_ok <- rep_collasso$METRICHE_SCALA["Rami Recisi per Esclusione"] > 0
  cat(sprintf("  %-50s : %s\n", "Capacità di rilevamento anomalie (Sensibilità)", 
              ifelse(sensibilita_ok, "APPROVATO [Rami isolati correttamente]", "FALLITO")))
  
  quote_volumi <- rep_caos$VOLUMI_MODALI$Quota_Percentuale
  bilanciamento_ok <- all(quote_volumi > 0)
  cat(sprintf("  %-50s : %s\n", "Bilanciamento Spaziale Mondi Modali (Box/Diamond)", 
              ifelse(bilanciamento_ok, "APPROVATO [Nessun volume vuoto]", "FALLITO")))
  
  cat("========================================================================\n")
}

# 3. ATTIVAZIONE DELLO STRESS TEST SULL'ENGINE SELEZIONATO
# Nota: Modifica il nome se la funzione dentro engine_2.0.R ha un nome diverso
Valida_Motore_PsiU(PsiU_Complete_MultiLibrary_V3)

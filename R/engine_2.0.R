#' @title PsiU Theoretical Engine V3 - MultiLibrary & HoTT Compliance
#' @description Implementazione rigorosa e imparziale del framework PsiU con partizione
#' multilibrary e verifica di risonanza tramite la regola J di Martin-Löf.
#' @param raw_input_vector Vettore numerico del flusso macro-volume da analizzare.
#' @param block_size Dimensione numerica del singolo blocco temporale (default = 50000).
#' @param critical_threshold Soglia teorica di vicinanza minima (default = 71.07).
PsiU_Complete_MultiLibrary_V3 <- function(raw_input_vector, block_size = 50000, critical_threshold = 71.07) {
  
  # 1. PARAMETRI GEOMETRICI E COSTANTI DELL'UNIVERSO LOGICO (Sezioni 1 e 2)
  MATTER_THRESHOLD <- 1/3
  SPACE_THRESHOLD  <- 2/3
  G_COSMIC         <- (sqrt(5) - 1) / 3  # Costante Gnomonica (~0.4120227)
  
  N_total  <- length(raw_input_vector)
  n_blocks <- floor(N_total / block_size)
  
  # STRUTTURA MULTILIBRARY (DNA DI BASE) - Tre librerie indipendenti e separate
  MULTILIBRARY <- list(
    "M1" = numeric(0),
    "M2" = numeric(0),
    "M3" = numeric(0)
  )
  
  # Inizializzazione dei contatori per i volumi modali totali
  volumi_box <- 0; volumi_diamond <- 0; volumi_transizione <- 0; volumi_vuoto <- 0
  rami_recisi <- 0
  
  indici_vicinanza_storici <- numeric(n_blocks)
  scostamenti_medi_storici <- numeric(n_blocks)
  valori_risonanza_storici <- numeric(n_blocks)
  
  # Normalizzazione Globale del Campo Continuo (Invarianza di scala)
  min_globale <- min(raw_input_vector)
  max_globale <- max(raw_input_vector)
  rng_globale <- max_globale - min_globale
  if (rng_globale == 0) rng_globale <- 1
  
  # 2. ELABORAZIONE SEQUENZIALE PER BLOCCHI TEMPORALI
  for (b in 1:n_blocks) {
    idx_start <- ((b - 1) * block_size) + 1
    idx_end   <- b * block_size
    block_grezzo <- raw_input_vector[idx_start:idx_end]
    
    # Mappatura sul dominio normalizzato U [0, 1]
    val_p <- (block_grezzo - min_globale) / rng_globale
    
    # Valutazione dei predicati introduzione (Coprodotto Box + Space)
    is_box         <- val_p <= MATTER_THRESHOLD
    is_vuoto       <- val_p > SPACE_THRESHOLD
    in_space       <- !is_box & !is_vuoto
    
    # Definizione geometrica del tipo DIAMOND nell'intorno continuo
    diamond_tolerance <- (SPACE_THRESHOLD - MATTER_THRESHOLD) * 0.5 
    dist_g            <- abs(val_p - G_COSMIC)
    is_diamond        <- in_space & (dist_g <= diamond_tolerance)
    is_transizione    <- in_space & !is_diamond
    
    # Aggiornamento accumulativo dei volumi macroscopici
    volumi_box         <- volumi_box + sum(is_box)
    volumi_diamond     <- volumi_diamond + sum(is_diamond)
    volumi_transizione <- volumi_transizione + sum(is_transizione)
    volumi_vuoto       <- volumi_vuoto + sum(is_vuoto)
    
    diamond_grezzo <- block_grezzo[is_diamond]
    
    # --------------------------------------------------------------------------
    # FASE 1: PRIMI 3 STEP - CRISTALLIZZAZIONE NELLA MULTILIBRARY
    # --------------------------------------------------------------------------
    if (b <= 3) {
      # Ogni blocco iniziale riempie la sua rispettiva partizione di libreria (M1, M2, M3)
      lib_name <- paste0("M", b)
      MULTILIBRARY[[lib_name]] <- block_grezzo[is_box | is_diamond]
      
      valori_risonanza_storici[b] <- mean(block_grezzo)
      indici_vicinanza_storici[b] <- critical_threshold
      scostamenti_medi_storici[b] <- 0
      
    } else {
      # --------------------------------------------------------------------------
      # FASE 2: DAL 4° STEP IN POI - RISONANZA MULTILIBRARY E REGOLA J
      # --------------------------------------------------------------------------
      # Estraiamo i target reali di risonanza (le medie reali di M1, M2, M3)
      target_M1 <- mean(MULTILIBRARY$M1)
      target_M2 <- mean(MULTILIBRARY$M2)
      target_M3 <- mean(MULTILIBRARY$M3)
      
      # La firma di risonanza globale del sistema è data dalla sintesi della libreria
      firma_risonanza_fissa <- mean(c(target_M1, target_M2, target_M3))
      
      if (length(diamond_grezzo) > 0) {
        # Regola J estesa: Confrontiamo il blocco con CIASCUNA libreria di memoria
        scostamento_M1 <- mean(abs(diamond_grezzo - target_M1))
        scostamento_M2 <- mean(abs(diamond_grezzo - target_M2))
        scostamento_M3 <- mean(abs(diamond_grezzo - target_M3))
        
        # Lo scostamento di risonanza effettivo valuta la sintonia minima (o massima vicinanza)
        scostamento_reale_minimo <- min(scostamento_M1, scostamento_M2, scostamento_M3)
        
        # Calcolo dell'indice di vicinanza geometrico inverso
        vicinanza_blocco <- (1 - (scostamento_reale_minimo / rng_globale)) * 100
        
        # CRITERIO DI POTATURA OMOTOPIA (Equazione 5)
        if (vicinanza_blocco < critical_threshold) {
          rami_recisi <- rami_recisi + 1
        }
        
        indici_vicinanza_storici[b] <- vicinanza_blocco
        scostamenti_medi_storici[b] <- scostamento_reale_minimo
      } else {
        # Se il tipo è vuoto, collassa sul tipo 0 (Formal Contradiction) -> Pruning immediato
        indici_vicinanza_storici[b] <- 0
        scostamenti_medi_storici[b] <- rng_globale
        rami_recisi <- rami_recisi + 1
      }
      valori_risonanza_storici[b] <- firma_risonanza_fissa
    }
  }
  
  # 3. COMPILAZIONE COMPONENTI DEL REPORT FINALE IMPARZIALE
  report <- list(
    STRUTTURA_ALBERO = c(
      "Volume Totale Analizzato" = N_total,
      "Rami Recisi per Esclusione" = rami_recisi
    ),
    VOLUMI_MODALI = data.frame(
      Volume_Assoluto = c(volumi_box, volumi_diamond, volumi_transizione, volumi_vuoto),
      Quota_Percentuale = c((volumi_box/N_total)*100, (volumi_diamond/N_total)*100, (volumi_transizione/N_total)*100, (volumi_vuoto/N_total)*100),
      row.names = c("BOX (Materia)", "DIAMOND (Ereditarietà)", "TRANSIZIONE OMOTOPICA", "VUOTO ESPANSIVO")
    ),
    DIAGNOSTICA_MULTILIBRARY = c(
      "FIRMA REALE DI RISONANZA (TARGET FISSO)" = tail(valori_risonanza_storici, 1),
      "Scostamento Medio dal DNA Multilibrary"   = mean(scostamenti_medi_storici[4:n_blocks], na.rm=TRUE),
      "Indice di Vicinanza Generale al Presente" = mean(indici_vicinanza_storici[4:n_blocks], na.rm=TRUE)
    )
  )
  return(report)
}

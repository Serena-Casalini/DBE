from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT, pair
import timeit
import matplotlib.pyplot as plt
 
#############################################
# Setup: genera i parametri pubblici
# Riferimento: Setup(1^λ, 1^L) nel documento
#############################################
def Setup(lambda_param, L):
    # Inizializziamo il gruppo bilineare di tipo 'MNT224'
    group = PairingGroup('MNT224')
   
    # Generiamo gli elementi di base g1 in G1 e g2 in G2
    g1 = group.random(G1)
    g2 = group.random(G2)
   
    # Campioniamo l'esponente segreto α da Z_p (il campo degli interi modulo p)
    alpha = group.random(ZR)
   
    # pp1: per G1 – memorizziamo [α^j]_1 per j = 1,...,L
    # (riferimento: [α]_1, …, [α^L]_1)
    pp1 = {}
    for j in range(1, L+1):
        # Eleviamo g1 a (α^j) per ottenere [α^j]_1
        pp1[j] = g1 ** (alpha ** j)
   
    # pp2: per G2 – memorizziamo:
    #   per j = 1,...,L: [α^j]_2
    #   per j = L+2,...,2L: [α^j]_2
    # e definiamo pp2[2L+1] = elemento neutro in G2 (rappresenta [0]_2)
    # (riferimento: [α^L+2]_2, …, [α^2L]_2 e [0]_2)
    pp2 = {}
    for j in range(1, L+1):
        pp2[j] = g2 ** (alpha ** j)
    for j in range(L+2, 2*L+1):
        pp2[j] = g2 ** (alpha ** j)
    pp2[2*L+1] = group.init(G2, 1)  # elemento neutro in G2
   
    return (group, L, g1, g2, alpha, pp1, pp2)
 
#############################################
# KeyGen: genera le chiavi per l'utente j
# Riferimento: KeyGen(pp, j) nel documento
#############################################
def KeyGen(pp, j):
    group, L, g1, g2, alpha, pp1, pp2 = pp
    # Campioniamo il segreto t_j da Z_p
    # ho usato il nome t al posto di t_j per comodità
    t = group.random(ZR)
  
    # Calcoliamo la chiave segreta: usk_j = [t * α^(L+1-j)]_2
    # (riferimento: usk_j = [t_jα^(L+1−j)]_2)
    usk = pp2[L+1-j] ** t  # equivalenza: g2 ** (t * (alpha ** (L+1 - j)))
   
    # Generiamo la chiave pubblica:
    # Componente in G1: upk_first = [t]_1
    upk_first = g1 ** t
    # Componenti in G2: per ogni l = 1,...,L tranne l = L+1-j,
    # upk_{j,l} = [t * α^l]_2
    # (riferimento: upk_j = ([t_j]_1, [t_jα]_2, …, [t_jα^(L+1-j-1)]_2, [t_jα^(L+1-j+1)]_2, …, [t_jα^L]_2))
    upk_components = {}
    for l in range(1, L+1):
        if l == (L+1 - j):
            continue  # saltiamo l'esponente "mancante" come da specifica
        upk_components[l] = pp2[l] ** t  # equivalente a g2 ** (t * (alpha ** l))
   
    # Restituiamo anche t (lo scalare) per semplificare i calcoli in fase di cifratura
    return (t, usk, (upk_first, upk_components))
 
#############################################
# Enc: cifratura
# Riferimento: Enc(pp, {upk}_j∈S, S, M) nel documento
#############################################
def Enc(pp, public_keys, S, M):
    """
    public_keys: dizionario che associa ogni utente j in S
                 alla tripla (t_j, usk_j, upk_j) dove
                 upk_j = (upk_first, upk_components)
    S: lista degli indici degli utenti destinatari (es. [1,2])
    M: messaggio in GT
    """
    group, L, g1, g2, alpha, pp1, pp2 = pp
   
    # Campioniamo s da Z_p
    s = group.random(ZR) 
   
    # ct1 = [s]_1, rappresenta l'elemento g1 elevato a s
    ct1 = g1 ** s
   
    # ct2 = ∏_{j in S} ( [s*t_j]_1 * ([α^j]_1)^s )
    # (riferimento: [s Ʃj∈S (t_j + α^j)]_1, calcolato come prodotto su j)
    ct2 = group.init(G1, 1)
    for j in S:
        t_j, _upk = public_keys[j]
        term1 = g1 ** (s * t_j)   # [s*t_j]_1
        term2 = pp1[j] ** s       # ([α^j]_1)^s
        ct2 *= term1 * term2
        # Nota: il prodotto cumulativo costruisce il valore richiesto

    # ct3 = [s*α^(L+1)]_T * M
    # Dove [s*α^(L+1)]_T si calcola tramite il pairing:
    # e( g1^(s*α), g2^(α^L) )
    ct3_factor = pair(g1 ** (s * alpha), g2 ** (alpha ** L))
    ct3 = ct3_factor * M
   
    return (ct1, ct2, ct3)
 
#############################################
# Dec: decifratura
# Riferimento: Dec(pp, {upk_j}j∈S, uski, ct, S, i) nel documento
#############################################
def Dec(pp, public_keys, usk_i, ct, S, i):
    """
    public_keys: dizionario come in Enc.
    usk_i: chiave segreta dell'utente i (già calcolata in KeyGen)
    ct: tuple del ciphertext (ct1, ct2, ct3)
    S: insieme degli utenti destinatari
    i: indice dell'utente per cui decriptare
    """
    group, L, g1, g2, alpha, pp1, pp2 = pp
    ct1, ct2, ct3 = ct
 
    # Calcoliamo pp_{2L+1-i} = [-α^(L+1-i)]_2, ossia l'inverso di pp2[L+1-i]
    pp_neg = pp2[L+1-i] ** -1
   
    # Il primo pairing: e( ct2^-1, pp_neg )
    pairing_1 = pair(ct2, pp_neg)


    # Inizializziamo il prodotto con la chiave segreta dell'utente i: usk_i = [t_iα^(L+1-i)]_2
    product = usk_i 
    # Per ogni j in S, j ≠ i, moltiplichiamo per:
    #   - upk_{j, L+1-i} = [t_jα^(L+1-i)]_2, componente della chiave pubblica di j
    #   - pp_{2L+1+j-i} = [α^(L+1+j-i)]_2 (dal Setup)
    for j in S:
        if j == i:
            continue
        t_j, upk_j = public_keys[j]
        # Recuperiamo la componente upk_{j,L+1-i} dalla chiave pubblica di j
        comp = upk_j[1].get(L+1 - i, None)
        if comp is None:
            raise Exception(f"Componente upk mancante per l'utente {j} per esponente {L+1-i}")
        pp_component = pp2[L+1+j-i]
        product *= comp * pp_component
   
    # Il secondo pairing: e( ct1, product )
    pairing_2 = pair(ct1, product)

    # Combiniamo i pairing per recuperare il messaggio:
    # M_dec = ct3 * e(ct2^-1, pp_neg) * e(ct1, product)
    M_dec = ct3 * pairing_1 * pairing_2
    return M_dec
 
#############################################
# Funzione di test
#############################################
def test():
    lambda_param = 128   # parametro di sicurezza
    L = 3                # numero di slot (utenti)
    pp = Setup(lambda_param, L)
    group, L, g1, g2, alpha, pp1, pp2 = pp
    print("[SETUP] Parametri generati con successo.")
   
    # Genera le chiavi per gli utenti in S (ad esempio, utenti 1 e 2)
    S = [1, 2]
    public_keys = {}  # per ogni j in S: (t_j, usk_j, upk_j)
    secret_keys = {}
    for j in S:
        t, usk, upk = KeyGen(pp, j)
        public_keys[j] = (t, upk)
        secret_keys[j] = usk
    print("[KEYGEN] Chiavi generate per gli utenti:", S)
 
    # Cifratura: scegli un messaggio casuale in GT
    M = group.random(GT)
    ct = Enc(pp, public_keys, S, M)
    print("[ENC] Cifratura completata.")
   
    # Decifratura per l'utente i=1
    M_dec = Dec(pp, public_keys, secret_keys[1], ct, S, 1)
    print("[DEC] Decifratura completata.")
   
    # Normalizziamo e confrontiamo i messaggi
    M_norm = group.deserialize(group.serialize(M))
    M_dec_norm = group.deserialize(group.serialize(M_dec))
   
    assert M_norm == M_dec_norm, "Errore: La decifratura non è corretta!"
    print("[SUCCESS] Decifratura corretta.")
 
#test()
def benchmark():
    lambda_param = 128
    L_values = [2, 3, 4, 5, 10, 20, 30]  # Varia L per testare diverse dimensioni\
    # Dati da raccogliere
    setup_times = []
    keygen_times = []
    enc_times = []
    dec_times = []

    for L in L_values:
        print(f"\n[Benchmarking per L = {L}]")
        
        # Misura Setup
        setup_time = timeit.timeit(lambda: Setup(lambda_param, L), number=5) / 5
        print(f"Setup time: {setup_time:.6f} sec")
        setup_times.append(setup_time)

        pp = Setup(lambda_param, L)
        S = list(range(1, min(3, L+1)))  # Seleziona 2 utenti se possibile

        # Misura KeyGen
        def keygen_test():
            public_keys = {}
            secret_keys = {}
            for j in S:
                t, usk, upk = KeyGen(pp, j)
                public_keys[j] = (t, upk)
                secret_keys[j] = usk
            return public_keys, secret_keys
        
        keygen_time = timeit.timeit(keygen_test, number=5) / 5
        print(f"KeyGen time: {keygen_time:.6f} sec")
        keygen_times.append(keygen_time)

        public_keys, secret_keys = keygen_test()
        M = pp[0].random(GT)  # Messaggio casuale in GT

        # Misura Enc
        enc_time = timeit.timeit(lambda: Enc(pp, public_keys, S, M), number=5) / 5
        print(f"Enc time: {enc_time:.6f} sec")
        enc_times.append(enc_time)

        ct = Enc(pp, public_keys, S, M)

        # Misura Dec
        dec_time = timeit.timeit(lambda: Dec(pp, public_keys, secret_keys[S[0]], ct, S, S[0]), number=5) / 5
        print(f"Dec time: {dec_time:.6f} sec")
        dec_times.append(dec_time)

    # Creazione del grafico
    plt.figure(figsize=(8, 5))
    plt.plot(L_values, setup_times, marker='o', label="Setup")
    plt.plot(L_values, keygen_times, marker='s', label="KeyGen")
    plt.plot(L_values, enc_times, marker='^', label="Enc")
    plt.plot(L_values, dec_times, marker='d', label="Dec")

    # Personalizzazione del grafico
    plt.xlabel("L (Numero di slot)")
    plt.ylabel("Tempo di esecuzione (s)")
    plt.title("Benchmark delle funzioni in base a L")
    plt.legend()
    plt.grid(True)

    # Mostra il grafico
    plt.show()

benchmark()

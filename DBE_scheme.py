from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT, pair


#! La differenza nasce dal modo in cui vengono “distribuite” le operazioni esponenziali nella libreria Charm
# se sono uguali o no dipende da come e quando vengono effettuate le operazioni di esponenziazione e a come vengono memorizzati i risultati all'interno della libreria

#############################################
# Setup: genera i parametri pubblici
#############################################
def Setup(lambda_param, L):
    group = PairingGroup('MNT224')
    g1 = group.random(G1)
    g2 = group.random(G2)
    alpha = group.random(ZR)
    
    # pp1: per G1 – memorizziamo [α^j]_1 per j = 1,...,L
    pp1 = {} #{} struttura dizionario (associa chiavi e valore)
    for j in range(1, L+1):
        pp1[j] = g1 ** (alpha ** j)
    
    # pp2: per G2 – memorizziamo:
    #   per j = 1,...,L: [α^j]_2
    #   per j = L+2,...,2L: [α^j]_2
    # e definiamo pp2[2L+1] = elemento neutro in G2.
    pp2 = {}
    for j in range(1, L+1):
        pp2[j] = g2 ** (alpha ** j)
    for j in range(L+2, 2*L+1):
        pp2[j] = g2 ** (alpha ** j)
    pp2[2*L+1] = group.init(G2, 1)
    
    return (group, L, g1, g2, alpha, pp1, pp2)

#############################################
# KeyGen: genera le chiavi per l'utente j
#############################################
def KeyGen(pp, j):
    group, L, g1, g2, alpha, pp1, pp2 = pp
    t = group.random(ZR)
    # Chiave segreta: usk_j = [t * α^(L+1-j)]_2
    usk = pp2[L+1-j]**t #! g2 ** (t * (alpha ** (L+1 - j)))
    #i valori sono diversi ma il confronto da "usk é uguale"
    '''print("usk", g2 ** (t * (alpha ** (L+1 - j))))
    print("prova", pp2[L+1-j]**t)
    if (g2 ** (t * (alpha ** (L+1 - j)))) == pp2[L+1-j]**t:
        print("usk é uguale")
    else:
        print("usk NON corrisponde")'''

    # Chiave pubblica:
    #   - componente in G1: upk_first = [t]_1
    #   - componenti in G2: per ogni l = 1,...,L tranne l = L+1-j, 
    #     upk_{j,l} = [t * α^l]_2
    upk_first = g1 ** t
    upk_components = {}
    for l in range(1, L+1):
        if l == (L+1 - j):
            continue  # saltiamo l'esponente "mancante"
        upk_components[l] = pp2[l]**t #! g2 ** (t * (alpha ** l))
        #i valori sono diversi ma il confronto da "usk é uguale"
        '''print("upk_components", l,  g2 ** (t * (alpha ** l)))
        print("prova1", pp2[l]**t)
        if ( g2 ** (t * (alpha ** l))) == pp2[l]**t:
            print("upk_component é uguale")
        else:
            print("upk NON corrisponde")'''
    # Restituiamo anche t (come scalare) per semplificare il calcolo in cifratura
    return (t, usk, (upk_first, upk_components))

#############################################
# Enc: cifratura
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
    s = group.random(ZR)
    
    # ct1 = [s]_1
    ct1 = g1 ** s
    
    # ct2 = ∏_{j in S} ( [s*t_j]_1 * ([α^j]_1)^s )
    ct2 = group.init(G1, 1)
    for j in S:
        t_j, _usk, _upk = public_keys[j]
        term1 = g1 ** (s * t_j) # [s*t_j]_1
        term2 = pp1[j] ** s   # ([α^j]_1) #? ci va il **s o no?
        ct2 *= term1 * term2
        #print("term1", term1)
        #\print("term2", term2)
    
    # ct3 = [s*α^(L+1)]_T * M, dove [s*α^(L+1)]_T = e( g1^(s*α), g2^(α^L) )
    # g2 ** (alpha ** L) = pp2[L]
    ct3_factor = pair(g1 ** (s * alpha), g2 ** (alpha ** L)) #pair(g1 ** (s * alpha), g2 ** (alpha ** L), group.Pairing)
    print("ct3_factor", ct3_factor)
    print("ct3_factor", 1/ct3_factor)
    #uguale a print("TEST", group.pair_prod([g1 ** (s * alpha)], [pp2[L]]))
    ct3 = ct3_factor * M
    
    return (ct1, ct2, ct3)

#############################################
# Dec: decifratura
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

    # Calcola pp_{2L+1-i} = [-α^(L+1-i)]_2 = g2^(-α^(L+1-i))
    pp_neg = pp2[L+1-i] ** -1 #!g2 ** ( - (alpha ** (L+1 - i)) )
    #i valori sono diversi ma il confronto da "pp_neg é corretto"
    '''print("pp_neg", pp2[L+1-i]**-1)
    print("g2 ** ( - (alpha ** (L+1 - i)))", g2 ** ( - (alpha ** (L+1 - i)) ))
    if pp_neg == pp2[L+1-i] ** -1:
        print("pp_neg è corretto")
    else:
        print("pp_neg NON corrisponde all'inverso di pp2[L+1-i]")'''
    pairing_1 = pair(ct2 ** -1,pp_neg) #pair(ct2 ** -1,pp_neg,group.Pairing)
    #print("pairing_1:", pairing_1)   
    #uguale a print("TEST", group.pair_prod([ct2 ** -1], [pp_neg]))
    # verifica print(ct2 * ct2**-1) ha output 0
    
    
    # Calcola il prodotto per il secondo pairing:
    # Partiamo con la chiave segreta dell'utente i: usk_i 
    # (uguale a partire con product = [0]_2 e moltiplicare alla fine con usk_i)
    product = usk_i  
    # Per ogni j in S, j ≠ i, moltiplichiamo per:
    #   upk_{j, L+1-i} (presente nella chiave pubblica di j)
    #   pp_{2L+1+j-i} = [α^(L+1+j-i)]_2 = g2^(α^(L+1+j-i))
    for j in S:
        if j == i:
            continue
         # upk_j = public_keys[j][2]
        t_j, usk_j, upk_j = public_keys[j]
        # upk_j è una tupla: (upk_first, upk_components)
        comp = upk_j[1].get(L+1 - i, None)
        #print("upk_j",upk_j)
        #print("COMP", comp)
        # uguale a print("VERIFICA", g2 ** ( t_j * ( alpha ** (L+1-i))) )
        if comp is None:
            raise Exception(f"Componente upk mancante per l'utente {j} per esponente {L+1-i}")
        pp_component = pp2[ L+1+j-i ] # g2 ** (alpha ** (L+1 + j - i)) 
        #print("pp_component", pp_component)
        #print("g2 ** (alpha ** (L+1 + j - i))", g2 ** (alpha ** (L+1 + j - i)) )
 
        product *= comp * pp_component
    #print("product: ", product)

    
    pairing_2 = pair(ct1,product) #pair(ct1,product,group.Pairing)
    #print("pairing_2:", pairing_2)   
    print("pairings:", pairing_1 * pairing_2)   
    #uguale a print("TEST", group.pair_prod([ct1], [product]))
  
    M_dec = ct3 * pairing_1 * pairing_2
    return M_dec

#############################################
# Funzione di test
#############################################
def test():
    lambda_param = 128   # parametro di sicurezza
    L = 3               # numero di slot (utenti)
    pp = Setup(lambda_param, L)
    group, L, g1, g2, alpha, pp1, pp2 = pp 
    print("[SETUP] Parametri generati con successo.")
    '''print("group:", group)
    print("g1:", g1)
    print("g2:", g2)
    print("alpha:", alpha)
    print("pp1:", pp1)
    print("pp2:", pp2)'''

    # Genera le chiavi per gli utenti in S (ad es. utenti 1 e 2)
    S = [1,2]
    public_keys = {}  # per ogni j in S: (t_j, usk_j, upk_j)
    secret_keys = {}
    for j in S:
        t, usk, upk = KeyGen(pp, j)
        public_keys[j] = (t, usk, upk)
        secret_keys[j] = usk
        '''print("public_keys", j , public_keys[j])
        print("secret_keys", j , secret_keys[j])
        print("t", t)
        print("usk", usk)
        print("upk", upk)'''
    print("[KEYGEN] Chiavi generate per gli utenti:", S)
    #print("public_keys", public_keys)

    # Cifratura: scegli un messaggio casuale in GT
    M = group.random(GT)
    #print("Messaggio M:", M)
    ct = Enc(pp, public_keys, S, M)
    print("[ENC] Cifratura completata.")
    (ct1,ct2,ct3) = ct
    '''print("ct1", ct1)
    print("ct2", ct2)
    print("ct3", ct3)'''
    
     # Decifratura per l'utente i=1
    M_dec = Dec(pp, public_keys, secret_keys[1], ct, S, 1)
    print("[DEC] Decifratura completata.")
    #print("M_dec", M_dec)
    M_norm = group.deserialize(group.serialize(M))
    M_dec_norm = group.deserialize(group.serialize(M_dec))

    #print("M_norm:", group.serialize(M_norm))
    #print("M_dec_norm:", group.serialize(M_dec_norm))
    assert M_norm == M_dec_norm, "Errore: La decifratura non è corretta!"
    print("[SUCCESS] Decifratura corretta.")

test()

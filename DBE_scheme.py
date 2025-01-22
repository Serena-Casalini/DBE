from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT
import hashlib

#LEGENDA COMMENTI
#? dubbi
#! probabili errori
#TODO idee da implementare/verificare
#* correzioni
#~ debug
# spiegazione codice

#* tolto per usare la funzione hash di libreria charm
def mess_to_hash(message):
    # Usa una funzione di hash per convertire il messaggio in un numero
    digest = hashlib.sha256(message.encode()).digest()
    # Converte l'hash in un intero
    return int.from_bytes(digest, byteorder='big')

def GT_element_to_hash(gt_element, group):
    #* tolto per usare la funzione hash di libreria charm
    '''# Serializza l'elemento del gruppo GT in bytes e calcola il suo hash
    gt_bytes = group.serialize(gt_element)
    #~ print("GT Element bytes:", gt_bytes)
    hash_bytes = hashlib.sha256(gt_bytes).digest()
    #~ print("Hash bytes from GT element:", hash_bytes) #Debug: Stampa il digest
    return int.from_bytes(hash_bytes, byteorder='big')'''
    # Combina serializzazione e hash in ZR
    return group.hash(group.serialize(gt_element), type=0)


#crea un'istanza del gruppo crittografico utilizzando un particolare schema di accoppiamento bilineare
group = PairingGroup('MNT224') #? forse meglio usare BN254(+sicuro ma +complicato)

def Setup(lambda_param, L):
    g1 = group.random(G1)
    g2 = group.random(G2)
    alpha = group.random(ZR)

    pp1 = [g1 ** (alpha ** i) for i in range(1, L+1)] # prende da 1 a L+1(escluso)
    pp2 = [g2 ** (alpha ** i) for i in range(1, 2*L + 1) if i != L + 1] #!forse L+1 non deve essere escluso?

    # Aggiungi l'elemento neutro [0]_2 alla posizione 2L+1 di pp2
    pp2.insert(2 * L, g2 ** 0) #g2 ** 0 rappresenta l'elemento neutro in G2

    return (g1, g2, pp1, pp2, alpha, L)

def KeyGen(pp, j):
    g1, g2, pp1, pp2, alpha, L = pp
    tj = group.random(ZR)

    # Chiave segreta uskj = [tj * α^(L+1-j)]_2
    uskj = pp2[L-j] ** tj

    # Chiave pubblica upkj = [tj]_1, [tj * α^l]_2 per l != L+1-j
    upkj_1 = g1 ** tj
    upkj_rest = [pp2[l-1] ** tj for l in range(1, L+1) if l != L+1-j]

    return (uskj, (upkj_1, upkj_rest))

def Enc(pp, upk_list, S, M):
    g1, g2, pp1, pp2, alpha, L = pp
    s = group.random(ZR)
    
    # Calcola [s * α^(L+1)]_T = e([sα]_1, [α^L]_2)
    s_alpha_L = g1 ** (s * alpha)
    pairing_result = group.pair_prod([s_alpha_L], [pp2[L-1]])

    #* tolto per usare la funzione hash di libreria charm
    '''# Hash del messaggio in un numero
    M_hashed = mess_to_hash(M)

    # Trasforma l'hash in un elemento del gruppo G1
    M_hashed_g1 = g1 ** M_hashed

    # Trasforma l'elemento in G1 in un elemento di GT usando l'accoppiamento
    M_hashed_gt = group.pair_prod([M_hashed_g1], [g2])'''

    #TODO per evitare di usare funzioni di hash esterne, 
    #TODO usare il passaggio di .hash() passando per ZR. riusarlo anche nella funzione GT_element_to_hash in modo inverso
    # Usa hash() per trasformare M in un elemento di G1
    M_hashed = group.hash(M, type=0)

    #Trasforma M_hashed_g1 in un elemento di GT
    M_hashed_gt = group.pair_prod(g1 ** M_hashed, g2)

    print("M_hashed (numero):", M_hashed)
    print("M_hashed_gt (GT):", M_hashed_gt)
    print("Pairing durante cifratura:", pairing_result)
    print("type pairing_result:", type(pairing_result))
    print("type pairing_result:", pairing_result.type)  # Conferma che è un elemento di tipo GT

    # Calcola [s * α^(L+1)]_T * M_hashed_gt
    ct3 = pairing_result * M_hashed_gt
    # Calcola [s]_1
    ct1 = g1 ** s

    # calcola [s * Σ_j∈S (tj + α^j)]_1
    ct2 = g1
    for j in S:
        tj, _ = upk_list[j-1]
        # Calcola [s t_j]_1 e [α^j]_1
        stj_1 = tj ** s
        alpha_j_1 = pp1[j-1]
        ct2 *= stj_1 * alpha_j_1

    return (ct1, ct2, ct3)

def Dec(pp, upk_list, uski, ct, S, i):
    g1, g2, pp1, pp2, alpha, L = pp  # Estrae parametri pubblici
    ct1, ct2, ct3 = ct               # Estrae componenti testo cifrato

    # Calcola l'inverso di ct2
    ct2_inv = ct2 ** -1

    # Calcola e(ct2_inv, pp2[L+1-i])
    if L - i < len(pp2):
        pairing_1 = group.pair_prod(ct2_inv, pp2[L - i] ** -1) #rappresenta [-α^(L+1-i)]_2
    else:
        raise IndexError(f"Index {L-i} is out of bounds for pp2 with length {len(pp2)}")

    # Inizializza il prodotto come l'elemento identità in G2 (identitȧ moltiplicativq nel pairing group)
    product = group.init(G2, 1) #? meglio g2 ** 0 o é indifferente?

    # Calcola il prodotto e(ct1, uski * product) su tutti gli utenti in S eccetto i
    for j in S:
        if j != i:
            # upk_list[j-1] = utente j
            # upk_list[j-1][1] = upkj_rest di utente j
            # upk_list[j-1][1][L-i] = upkj_rest[L-i] di utente j se L+1-i < L+1-j
            # upk_list[j-1][1][L-i-1] = upkj_rest[L-i-1] di utente j se L+1-i > L+1-j
            if (L - i - 1) < len(upk_list[j-1][1]) and (L + j - i) < len(pp2):
                # Determina la parte corretta di upk_j e pp2 in base agli indici utente
                upkj_part = upk_list[j-1][1][L - i] if L + 1 - i < L + 1 - j else upk_list[j-1][1][L - i - 1]
                pp2_part = pp2[L + j - i]

                # Aggiorna il prodotto in G
                product *= (upkj_part * pp2_part)
            else:
                raise IndexError(f"Index {L - i - 1} for upk or {L + j - i} for pp2 is out of bounds. "
                                 f"upk_list[j-1][1] has length {len(upk_list[j-1][1])}, pp2 has length {len(pp2)}.")

    # Calcola il secondo pairing: e(ct1, uski * product)
    pairing_2 = group.pair_prod(ct1, uski * product)

    '''print("Pairing durante decifratura (ct2_inv, pp2[L+1-i]):", pairing_1)
    print("Pairing durante decifratura (ct1, uski * prodotto):", pairing_2)'''

    # Ricostruisce il messaggio decifrato combinando i pairings
    M_dec = ct3 * pairing_1 * pairing_2  #Riconstruisce l'hash del messaggio dal testo cifrato

    return M_dec

def test():
    lambda_param = 128  # Parametro di sicurezza
    L = 3 # Numero massimo di utenti
    pp = Setup(lambda_param, L)
    g1, g2, pp1, pp2, alpha, L = pp 
    
    #~ debug funzione Setup
    '''print("g1 (random in G1):", g1)
    print("g2 (random in G2):", g2)
    print("pp1 (array di g1^alpha^i):", pp1)
    print("pp2 (array di g2^alpha^i, con g2^0 aggiunto):", pp2)
    print("alpha (random in ZR):", alpha)
    print("L (numero di utenti):", L)'''

    usk, upk = KeyGen(pp,1) #chiavi per utente 1
    
    M = "ciao" # messaggio stringa
    S = [1, 2]  # Utenti per cui cifrare il messaggio

    upk_list = [KeyGen(pp, i)[1] for i in S]  # Ottiene le chiavi pubbliche per gli utenti in S
    #~ debug funzione KeyGen
    '''print("Chiave segreta (usk):", usk)
    print("Chiave pubblica (upk):", upk)
    print("Chiavi pubbliche per gli utenti in S:", upk_list)'''

    # Ottiene il ciphertext
    ct = Enc(pp, upk_list, S, M)
    
    #~ debug funzione Enc
    '''print("Ciphertext (ct1):", ct[0])
    print("Ciphertext (ct2):", ct[1])
    print("Ciphertext (ct3):", ct[2])'''

    M_dec = Dec(pp, upk_list, usk, ct, S, 1)

    #* tolto per usare la funzione hash di libreria charm
    '''original_hashed = mess_to_hash(M)
    original_hashed_gt = group.pair_prod(g1 ** original_hashed, g2)'''

    #~ debug funzione Dec
    print("M_dec: ", M_dec)
    print("TYPE", type(M_dec))
    print("prova", M_dec.type) #conferma che é un elemento di tipo GT
    M_hashed = group.hash(M, type=0)
    M_hashed_gt = group.pair_prod(g1 ** M_hashed, g2) #Trasforma M_hashed in un elemento di GT
    print("Original Hashed:",M_hashed)
    print("Type", type(M_hashed))
    print("Original Hashed GT:", M_hashed_gt)
    print("Type", type(M_hashed_gt))
    print("prova", M_hashed_gt.type) #conferma che é un elemento di tipo GT
    '''# Confronta M_dec con l'hash originale del messaggio
    assert M_dec == M_hashed_gt, "Errore: La decifratura non è corretta."'''

test()

#? Forse il confronto finale non ha senso:
#? Questa differenza è attesa perché l'hash di un elemento di GT è un processo irreversibile 
#? rispetto all'hash diretto di un messaggio.

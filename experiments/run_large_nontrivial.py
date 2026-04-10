"""대규모 비자명 고정점 탐색: N=1000, 10000"""
import numpy as np, sys, os, time
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))

d = 5

def scf_with_levels(N, levels, max_steps=300, seed=42):
    np.random.seed(seed)
    psi = np.random.randn(N, d) + 1j * np.random.randn(N, d)
    psi /= np.linalg.norm(psi, axis=1, keepdims=True)
    
    for step in range(max_steps):
        G = psi @ psi.conj().T
        W = np.abs(G)**2 / d
        
        new_psi = np.zeros_like(psi)
        errs = []
        for i in range(N):
            w = W[i].copy(); w[i] = 0
            H_i = (np.sqrt(w)[:, None] * psi).T @ (np.sqrt(w)[:, None] * psi).conj()
            evals, evecs = np.linalg.eigh(H_i)
            idx_sort = np.argsort(evals)[::-1]
            evecs = evecs[:, idx_sort]
            
            k = levels[i]
            new_psi_i = evecs[:, k]
            phase = np.vdot(new_psi_i, psi[i])
            if abs(phase) > 1e-10:
                new_psi_i *= np.conj(phase) / abs(phase)
            new_psi[i] = new_psi_i
            
            H_psi = H_i @ psi[i]
            lam = np.real(np.vdot(psi[i], H_psi))
            errs.append(np.linalg.norm(H_psi - lam * psi[i]))
        
        mean_err = np.mean(errs)
        psi = new_psi
        
        if step % 20 == 0:
            print(f"    step {step:3d}: err={mean_err:.6f}", flush=True)
        if mean_err < 1e-10:
            print(f"    수렴! step {step}")
            break
    
    G_final = psi @ psi.conj().T
    return psi, G_final, mean_err, step+1

results_dir = os.path.join(os.path.dirname(__file__), "..", "results", "solutions")
os.makedirs(results_dir, exist_ok=True)

for N in [1000, 10000]:
    print(f"\n{'='*70}")
    print(f"  N = {N}")
    print(f"{'='*70}")
    
    np.random.seed(99)
    levels = list(np.random.randint(0, 5, N))
    
    max_steps = 150 if N <= 1000 else 50
    
    t0 = time.time()
    psi, G, err, steps = scf_with_levels(N, levels, max_steps=max_steps, seed=99)
    elapsed = time.time() - t0
    
    # G 고유값
    eigs_G = np.sort(np.linalg.eigvalsh(G))[::-1][:d]
    
    # W 통계
    W = np.abs(G)**2 / d
    mask = ~np.eye(N, dtype=bool)
    w_off = W[mask]
    
    # 홀로노미
    hols = []
    for _ in range(2000):
        i,j,k = np.random.choice(N, 3, replace=False)
        hols.append(abs(np.angle(G[i,j] * G[j,k] * G[k,i])))
    
    print(f"\n  시간: {elapsed:.1f}s, steps: {steps}, err: {err:.6f}")
    print(f"  G 고유값: {eigs_G}")
    print(f"  W: mean={w_off.mean():.5f}, std={w_off.std():.5f}, CV={w_off.std()/w_off.mean():.4f}")
    print(f"  홀로노미: {np.mean(hols):.4f}")
    
    # 저장
    fname = os.path.join(results_dir, f"universe_N{N}_seed99_nontrivial.npz")
    np.savez_compressed(fname,
        psi=psi, eigenvalues_G=eigs_G,
        levels=np.array(levels),
        N=N, d=d, seed=99, steps=steps, err=err,
        W_mean=w_off.mean(), W_std=w_off.std(),
        holonomy_mean=np.mean(hols),
    )
    size_mb = os.path.getsize(fname) / 1024 / 1024
    print(f"  저장: {fname} ({size_mb:.1f} MB)")

print("\n완료!")

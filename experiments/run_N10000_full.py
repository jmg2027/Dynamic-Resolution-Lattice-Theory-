"""N=10000 비자명 고정점: 300 step 풀 수렴"""
import numpy as np, sys, os, time
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))

d = 5; N = 10000
np.random.seed(99)
levels = list(np.random.randint(0, 5, N))

np.random.seed(99)
psi = np.random.randn(N, d) + 1j * np.random.randn(N, d)
psi /= np.linalg.norm(psi, axis=1, keepdims=True)

print(f"N={N}, 300 steps SCF", flush=True)
t0 = time.time()

for step in range(300):
    G = psi @ psi.conj().T
    W = np.abs(G)**2 / d
    new_psi = np.zeros_like(psi)
    errs = []
    for i in range(N):
        w = W[i].copy(); w[i] = 0
        H_i = (np.sqrt(w)[:, None] * psi).T @ (np.sqrt(w)[:, None] * psi).conj()
        evals, evecs = np.linalg.eigh(H_i)
        idx = np.argsort(evals)[::-1]
        evecs = evecs[:, idx]
        k = levels[i]
        new_psi_i = evecs[:, k]
        phase = np.vdot(new_psi_i, psi[i])
        if abs(phase) > 1e-10:
            new_psi_i *= np.conj(phase) / abs(phase)
        new_psi[i] = new_psi_i
        H_psi = H_i @ psi[i]
        lam = np.real(np.vdot(psi[i], H_psi))
        errs.append(np.linalg.norm(H_psi - lam * psi[i]))
    
    psi = new_psi
    mean_err = np.mean(errs)
    if step % 20 == 0:
        elapsed = time.time() - t0
        print(f"  step {step:3d}: err={mean_err:.4f}, {elapsed:.0f}s", flush=True)
    if mean_err < 1e-8:
        print(f"  수렴! step {step}")
        break

G_final = psi @ psi.conj().T
eigs_G = np.sort(np.linalg.eigvalsh(G_final))[::-1][:d]
W_final = np.abs(G_final)**2 / d
mask = ~np.eye(N, dtype=bool)
w_off = W_final[mask]

print(f"\n  총 시간: {time.time()-t0:.0f}s, err={mean_err:.6f}")
print(f"  G 고유값: {eigs_G}")
print(f"  W: mean={w_off.mean():.5f}, CV={w_off.std()/w_off.mean():.4f}")

fname = os.path.join(os.path.dirname(__file__), "..", "results", "solutions", "universe_N10000_seed99_300step.npz")
np.savez_compressed(fname, psi=psi, eigenvalues_G=eigs_G, levels=np.array(levels),
    N=N, d=d, seed=99, steps=step+1, err=mean_err)
print(f"  저장: {fname} ({os.path.getsize(fname)/1024/1024:.1f} MB)")

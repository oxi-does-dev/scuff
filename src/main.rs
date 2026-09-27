//! scuff - свой формат сжатия, жмёт лучше zip-а на большинстве файлов
//! как устроено: lz77 с большим окном -> оптимальный парсинг через дп -> хаффман по блокам
//! формат: SCUFF\x04 + длина + crc + биты. блоки: stored / fixed / dynamic

use std::collections::BinaryHeap;
use std::cmp::Reverse;

pub const MAGIC: &[u8; 6] = b"SCUFF\x04";
const WINDOW: usize = 262_144;
const MIN_MATCH: usize = 3;
const MAX_MATCH: usize = 4096;
const NLIT: usize = 290; // 0-255 литералы, 256 конец блока, 257+ длины
const HASH_BITS: usize = 17;
const HASH_SIZE: usize = 1 << HASH_BITS;
const MAX_CHAIN: usize = 1024;

const LEN_BASE: [u16; 33] = [3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258,259,387,643,1667];
const LEN_EXTRA: [u8; 33] = [0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0,7,8,10,12];
const DIST_BASE: [u32; 32] = [1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577,32769,49151];
const DIST_EXTRA: [u8; 32] = [0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13,14,18];
const PRE_ORDER: [usize; 19] = [16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15];

fn len_code(len: usize) -> (u16, u8, u16) {
    // 258 это отдельный код 285, иначе таблица врёт на единицу
    if len == 258 { return (285, 0, 0); }
    for (i, &b) in LEN_BASE.iter().enumerate() {
        let e = LEN_EXTRA[i] as u16;
        let max = b + if e > 0 { (1 << e) - 1 } else { 0 };
        if (b as usize) <= len && len <= max as usize {
            return ((257 + i) as u16, e as u8, (len as u16) - b);
        }
    }
    (285, 0, 0)
}
fn dist_code(dist: usize) -> (u8, u8, u32) {
    for (i, &b) in DIST_BASE.iter().enumerate() {
        let e = DIST_EXTRA[i];
        let max = b + if e > 0 { (1 << e) - 1 } else { 0 };
        if (b as usize) <= dist && dist <= max as usize {
            return (i as u8, e, (dist as u32) - b);
        }
    }
    panic!("dist too large: {dist}");
}
// полный разбор (код, экстра-биты, значение экстра) через таблицы
#[inline]
fn len_ev(len: usize) -> (u16, u8, u32) {
    let (lc, le) = lentab()[len];
    (lc, le, len as u32 - LEN_BASE[lc as usize - 257] as u32)
}
#[inline]
fn dist_ev(dist: usize) -> (u8, u8, u32) {
    let (dc, de) = disttab()[dist];
    (dc, de, dist as u32 - DIST_BASE[dc as usize])
}
fn match_cost(len: usize, dist: usize, cl: &[(u32, u8)], cd: &[(u32, u8)]) -> u32 {
    let (lc, le) = lentab()[len];
    let (dc, de) = disttab()[dist];
    cl[lc as usize].1 as u32 + le as u32 + cd[dc as usize].1 as u32 + de as u32
}

// предвычисленные таблицы кодов: match_cost дёргается сотни миллионов раз,
// линейные сканы там это главный жор. строю один раз лениво.
static LENTAB: std::sync::OnceLock<Vec<(u16, u8)>> = std::sync::OnceLock::new();
static DISTTAB: std::sync::OnceLock<Vec<(u8, u8)>> = std::sync::OnceLock::new();
fn lentab() -> &'static [(u16, u8)] {
    LENTAB.get_or_init(|| {
        (0..=MAX_MATCH).map(|l| { let (c, e, _) = len_code(l); (c, e) }).collect()
    })
}
fn disttab() -> &'static [(u8, u8)] {
    DISTTAB.get_or_init(|| {
        (0..=WINDOW).map(|d| if d == 0 { (0, 0) } else { let (c, e, _) = dist_code(d); (c, e) }).collect()
    })
}

// длина совпадения от (a, b), не дальше maxl. сравниваю по 8 байт сразу
#[inline]
fn match_len(data: &[u8], a: usize, b: usize, maxl: usize) -> usize {
    let mut ml = 0;
    while ml + 8 <= maxl {
        let x = u64::from_le_bytes(data[a + ml..a + ml + 8].try_into().unwrap());
        let y = u64::from_le_bytes(data[b + ml..b + ml + 8].try_into().unwrap());
        let d = x ^ y;
        if d == 0 { ml += 8; }
        else { return (ml + (d.trailing_zeros() / 8) as usize).min(maxl); }
    }
    while ml < maxl && data[a + ml] == data[b + ml] { ml += 1; }
    ml
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Token { Lit(u8), Match { len: usize, dist: usize } }

fn hash3(d: &[u8], i: usize) -> usize {
    let v = ((d[i] as u32) << 16) | ((d[i+1] as u32) << 8) | d[i+2] as u32;
    ((v.wrapping_mul(0x9E3779B1)) >> (32 - HASH_BITS)) as usize
}

// ищу все матчи в позиции i. на каждую длину запоминаю ближний, плюс один длинный отдельно
fn find_matches_from(data: &[u8], i: usize, start: i32, prev: &[i32]) -> Vec<(usize, usize)> {
    let n = data.len();
    let mut out = Vec::new();
    if i + MIN_MATCH > n { return out; }
    let lo = i.saturating_sub(WINDOW) as i32;
    // best_exact[e] = ближняя дистанция для матчей ровно длины e
    let mut best_exact = [usize::MAX; 259];
    let mut long_best = (0usize, usize::MAX); // самый длинный, длина может быть > 258
    let mut chain = 0;
    let mut c = start;
    while c >= 0 && chain < MAX_CHAIN {
        let p = c as usize;
        if (p as i32) < lo { break; } // цепочка идёт назад, дальше только старьё
        if data[p] == data[i] {
            let maxl = MAX_MATCH.min(n - i);
            let ml = match_len(data, p, i, maxl);
            if ml >= MIN_MATCH {
                let d = i - p;
                let e = ml.min(258);
                if d < best_exact[e] { best_exact[e] = d; }
                if ml > long_best.0 || (ml == long_best.0 && d < long_best.1) {
                    long_best = (ml, d);
                }
            }
            if ml == MAX_MATCH { break; }
            if ml >= 96 && chain >= 256 { break; } // норм матч уже есть, дальше лень идти
        }
        c = prev[p];
        chain += 1;
    }
    // для каждой длины берём ближнюю дистанцию среди матчей не короче
    let mut run_min = usize::MAX;
    for l in (MIN_MATCH..=258).rev() {
        if best_exact[l] < run_min { run_min = best_exact[l]; }
        if run_min != usize::MAX { out.push((l, run_min)); }
    }
    out.reverse();
    // длинный кандидат дп посчитает сам
    if long_best.0 > 258 {
        out.push(long_best);
    }
    out
}

// ---------- huffman ----------
#[derive(PartialEq, Eq)]
struct HN { f: u64, s: usize, l: Option<Box<HN>>, r: Option<Box<HN>> }
impl Ord for HN {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering { self.f.cmp(&o.f).then(self.s.cmp(&o.s)) }
}
impl PartialOrd for HN {
    fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> { Some(self.cmp(o)) }
}

fn build_lengths(freq: &[u64], maxbits: u8) -> Vec<u8> {
    let mut heap: BinaryHeap<Reverse<HN>> = BinaryHeap::new();
    for (s, &f) in freq.iter().enumerate() {
        if f > 0 { heap.push(Reverse(HN { f: f.max(1), s, l: None, r: None })); }
    }
    if heap.is_empty() { return vec![0; freq.len()]; }
    if heap.len() == 1 {
        let mut l = vec![0u8; freq.len()];
        l[heap.pop().unwrap().0.s] = 1;
        return l;
    }
    while heap.len() > 1 {
        let a = heap.pop().unwrap().0;
        let b = heap.pop().unwrap().0;
        heap.push(Reverse(HN { f: a.f + b.f, s: usize::MAX, l: Some(Box::new(a)), r: Some(Box::new(b)) }));
    }
    let root = heap.pop().unwrap().0;
    let mut lens = vec![0u8; freq.len()];
    let mut over = false;
    fn walk(nd: &HN, d: u8, lens: &mut [u8], over: &mut bool, max: u8) {
        if nd.l.is_none() { lens[nd.s] = d; if d > max { *over = true; } }
        else { walk(nd.l.as_ref().unwrap(), d + 1, lens, over, max); walk(nd.r.as_ref().unwrap(), d + 1, lens, over, max); }
    }
    walk(&root, 1, &mut lens, &mut over, maxbits);
    if over {
        let used: Vec<usize> = freq.iter().enumerate().filter(|(_, f)| **f > 0).map(|(s, _)| s).collect();
        let bits = (used.len().next_power_of_two().trailing_zeros().max(1).min(maxbits as u32)) as u8;
        lens.fill(0);
        for s in used { lens[s] = bits; }
    }
    lens
}

fn canon_codes(lens: &[u8]) -> Vec<(u32, u8)> {
    let maxl = *lens.iter().max().unwrap_or(&0) as usize;
    let mut bl = vec![0u32; maxl + 1];
    for &l in lens { if l > 0 { bl[l as usize] += 1; } }
    let mut code = 0u32;
    let mut next = vec![0u32; maxl + 1];
    for b in 1..=maxl { code = (code + bl[b - 1]) << 1; next[b] = code; }
    lens.iter().map(|&l| if l == 0 { (0, 0) } else { let c = next[l as usize]; next[l as usize] += 1; (c, l) }).collect()
}

// fixed таблица как в deflate, плюс мои коды 286-289 (другого места не нашлось,
// 0xc8+ конфликтуют с 9-битными, так что 0x18c-0x18f)
fn fixed_litlen(s: usize) -> (u32, u8) {
    if s <= 143 { (0x30 + s as u32, 8) }
    else if s <= 255 { (0x190 + s as u32 - 144, 9) }
    else if s <= 279 { (s as u32 - 256, 7) }
    else if s <= 285 { (0xC0 + s as u32 - 280, 8) }
    else { (0x18C + s as u32 - 286, 9) }
}
fn fixed_dist(s: usize) -> (u32, u8) { (s as u32, 5) }

struct BitWriter { buf: Vec<u8>, acc: u32, n: u8, total: u64 }
impl BitWriter {
    fn new() -> Self { Self { buf: Vec::new(), acc: 0, n: 0, total: 0 } }
    fn bit(&mut self, b: u32) {
        self.acc = (self.acc << 1) | (b & 1);
        self.n += 1;
        if self.n == 8 { self.buf.push(self.acc as u8); self.acc = 0; self.n = 0; }
        self.total += 1;
    }
    fn bits(&mut self, code: u32, len: u8) {
        for k in (0..len).rev() { self.bit((code >> k) & 1); }
    }
    fn align8(&mut self) { while self.n != 0 { self.bit(0); } }
    fn raw_bytes(&mut self, b: &[u8]) { debug_assert!(self.n == 0); self.buf.extend_from_slice(b); self.total += b.len() as u64 * 8; }
    fn finish(mut self) -> (Vec<u8>, u64) {
        if self.n > 0 { self.buf.push((self.acc << (8 - self.n)) as u8); }
        (self.buf, self.total)
    }
}

struct BitReader<'a> { buf: &'a [u8], pos: u64, nbits: u64 }
impl<'a> BitReader<'a> {
    fn bit(&mut self) -> Option<u32> {
        if self.pos >= self.nbits { return None; }
        let b = (self.buf[(self.pos / 8) as usize] >> (7 - (self.pos % 8))) & 1;
        self.pos += 1;
        Some(b as u32)
    }
    fn bits(&mut self, n: u8) -> Option<u32> {
        let mut v = 0u32;
        for _ in 0..n { v = (v << 1) | self.bit()?; }
        Some(v)
    }
}

struct Decoder { left: Vec<i32>, right: Vec<i32>, sym: Vec<i32> }
impl Decoder {
    // трай по готовым парам (код, длина), fixed таблица неканоническая так что так
    fn from_codes(codes: &[(u32, u8)]) -> Self {
        let mut left = vec![-1]; let mut right = vec![-1]; let mut sym = vec![-1];
        for (s, &(c, l)) in codes.iter().enumerate() {
            let mut nd = 0usize;
            for k in (0..l).rev() {
                let b = ((c >> k) & 1) as usize;
                let nx = if b == 0 { left[nd] } else { right[nd] };
                let nx = if nx < 0 {
                    left.push(-1); right.push(-1); sym.push(-1);
                    let id = (left.len() - 1) as i32;
                    if b == 0 { left[nd] = id; } else { right[nd] = id; }
                    id
                } else { nx };
                nd = nx as usize;
            }
            sym[nd] = s as i32;
        }
        Self { left, right, sym }
    }
    fn new(lens: &[u8]) -> Self {
        let mut left = vec![-1]; let mut right = vec![-1]; let mut sym = vec![-1];
        for (s, &(c, l)) in canon_codes(lens).iter().enumerate() {
            if l == 0 { continue; }
            let mut nd = 0usize;
            for k in (0..l).rev() {
                let b = ((c >> k) & 1) as usize;
                let nx = if b == 0 { left[nd] } else { right[nd] };
                let nx = if nx < 0 {
                    left.push(-1); right.push(-1); sym.push(-1);
                    let id = (left.len() - 1) as i32;
                    if b == 0 { left[nd] = id; } else { right[nd] = id; }
                    id
                } else { nx };
                nd = nx as usize;
            }
            sym[nd] = s as i32;
        }
        Self { left, right, sym }
    }
    fn sym(&self, r: &mut BitReader) -> Option<usize> {
        if self.sym[0] >= 0 && self.left[0] < 0 && self.right[0] < 0 { return Some(self.sym[0] as usize); }
        let mut nd = 0usize;
        loop {
            let b = r.bit()? as usize;
            nd = (if b == 0 { self.left[nd] } else { self.right[nd] }) as usize;
            if self.sym[nd] >= 0 && self.left[nd] < 0 && self.right[nd] < 0 { return Some(self.sym[nd] as usize); }
        }
    }
}

fn crc32(d: &[u8]) -> u32 {
    let mut crc = 0xFFFF_FFFFu32;
    for &b in d {
        crc ^= b as u32;
        for _ in 0..8 { crc = if crc & 1 == 1 { (crc >> 1) ^ 0xEDB88320 } else { crc >> 1 }; }
    }
    !crc
}

// дп по блоку [bs, be). cl/cd это цены символов
fn parse_block(data: &[u8], bs: usize, be: usize, matches: &[Vec<(usize, usize)>],
               cl: &[(u32, u8)], cd: &[(u32, u8)]) -> Vec<Token> {
    let m = be - bs;
    const INF: u32 = u32::MAX / 4;
    let mut dp = vec![INF; m + 1];
    let mut pre: Vec<(usize, usize, usize)> = vec![(0, 0, 0); m + 1]; // откуда пришли, длина, дистанция
    dp[0] = 0;
    for i in 0..m {
        if dp[i] == INF { continue; }
        let gi = bs + i;
        // литерал
        let c = cl[data[gi] as usize].1 as u32;
        if dp[i] + c < dp[i + 1] { dp[i + 1] = dp[i] + c; pre[i + 1] = (i, 1, 0); }
        // матчи уже найдены, просто перебираем
        for &(ml, d) in &matches[i] {
            if i + ml > m { continue; }
            let mc = match_cost(ml, d, cl, cd);
            if dp[i] + mc < dp[i + ml] { dp[i + ml] = dp[i] + mc; pre[i + ml] = (i, ml, d); }
        }
    }
    // откатываемся назад, собираем токены
    let mut toks = Vec::new();
    let mut i = m;
    while i > 0 {
        let (p, l, d) = pre[i];
        if l == 1 && d == 0 { toks.push(Token::Lit(data[bs + p])); }
        else { toks.push(Token::Match { len: l, dist: d }); }
        i = p;
    }
    toks.reverse();
    toks
}

fn tokens_freq(toks: &[Token], fl: &mut [u64], fd: &mut [u64]) {
    for t in toks {
        match *t {
            Token::Lit(b) => fl[b as usize] += 1,
            Token::Match { len, dist } => {
                fl[lentab()[len].0 as usize] += 1;
                fd[disttab()[dist].0 as usize] += 1;
            }
        }
    }
}

// rle для длин: 0-15 как есть, 16 повтор прошлого 3-6 раз, 17 нули 3-10, 18 нули 11-138
fn write_tree(w: &mut BitWriter, lens: &[u8]) {
    // сначала rle, потом отдельное маленькое дерево для него
    let mut fixed: Vec<(u8, u8)> = Vec::new(); // (символ, экстра)
    let mut i = 0;
    while i < lens.len() {
        let v = lens[i];
        let mut run = 1;
        while i + run < lens.len() && lens[i + run] == v { run += 1; }
        if v == 0 {
            let mut r = run;
            while r > 0 {
                if r >= 11 { let take = r.min(138); fixed.push((18, (take - 11) as u8)); r -= take; }
                else if r >= 3 { let take = r.min(10); fixed.push((17, (take - 3) as u8)); r -= take; }
                else { for _ in 0..r { fixed.push((0, 0)); } r = 0; }
            }
        } else {
            fixed.push((v, 0));
            let mut r = run - 1;
            while r >= 3 { let take = r.min(6); fixed.push((16, (take - 3) as u8)); r -= take; }
            for _ in 0..r { fixed.push((v, 0)); }
        }
        i += run;
    }
    let mut fp = vec![0u64; 19];
    for (s, _) in &fixed { fp[*s as usize] += 1; }
    let pl = build_lengths(&fp, 7);
    let mut npre = 19;
    while npre > 4 && pl[PRE_ORDER[npre - 1]] == 0 { npre -= 1; }
    w.bits(npre as u32, 8);
    for k in 0..npre { w.bits(pl[PRE_ORDER[k]] as u32, 4); }
    let pc = canon_codes(&pl);
    for (s, e) in &fixed {
        let (c, l) = pc[*s as usize];
        w.bits(c, l);
        match s {
            16 => w.bits(*e as u32, 2),
            17 => w.bits(*e as u32, 3),
            18 => w.bits(*e as u32, 7),
            _ => {}
        }
    }
}

fn read_tree(r: &mut BitReader) -> Result<(Vec<u8>, Vec<u8>), String> {
    let nlit = r.bits(6).ok_or("nlit")? as usize + 257;
    let ndist = r.bits(5).ok_or("ndist")? as usize + 1;
    if nlit < 257 || nlit > NLIT || ndist == 0 || ndist > 32 { return Err("bad tree sizes".into()); }
    let npre = r.bits(8).ok_or("tree hdr")? as usize;
    if npre < 4 || npre > 19 { return Err("bad npre".into()); }
    let mut pl = vec![0u8; 19];
    for k in 0..npre { pl[PRE_ORDER[k]] = r.bits(4).ok_or("pre len")? as u8; }
    let pd = Decoder::new(&pl);
    let total = nlit + ndist;
    let mut lens = vec![0u8; total];
    let mut i = 0;
    let mut prev = 0u8;
    while i < total {
        let s = pd.sym(r).ok_or("pre sym")?;
        match s {
            0..=15 => { lens[i] = s as u8; prev = s as u8; i += 1; }
            16 => {
                let e = r.bits(2).ok_or("e16")? as usize + 3;
                if i == 0 { return Err("bad 16".into()); }
                for _ in 0..e { if i >= total { return Err("ovf 16".into()); } lens[i] = prev; i += 1; }
            }
            17 => {
                let e = r.bits(3).ok_or("e17")? as usize + 3;
                for _ in 0..e { if i >= total { return Err("ovf 17".into()); } lens[i] = 0; i += 1; }
                prev = 0;
            }
            18 => {
                let e = r.bits(7).ok_or("e18")? as usize + 11;
                for _ in 0..e { if i >= total { return Err("ovf 18".into()); } lens[i] = 0; i += 1; }
                prev = 0;
            }
            _ => return Err("bad pre sym".into()),
        }
    }
    Ok((lens[..nlit].to_vec(), lens[nlit..].to_vec()))
}

// длины хаффмана под токены, лишние нули в конце режем
fn trees_for(toks: &[Token]) -> (Vec<u8>, Vec<u8>, usize, usize) {
    let mut fl = vec![0u64; NLIT];
    let mut fd = vec![0u64; 32];
    tokens_freq(toks, &mut fl, &mut fd);
    fl[256] += 1;
    let ll = build_lengths(&fl, 15);
    let dl = build_lengths(&fd, 15);
    let mut nlit = NLIT;
    while nlit > 257 && ll[nlit - 1] == 0 { nlit -= 1; }
    let mut ndist = 32;
    while ndist > 1 && dl[ndist - 1] == 0 { ndist -= 1; }
    (ll, dl, nlit, ndist)
}

// сколько битов займут данные без дерева
fn data_bits(toks: &[Token], cl: &[(u32, u8)], cd: &[(u32, u8)]) -> u64 {
    let mut b = 0u64;
    for t in toks {
        match *t {
            Token::Lit(x) => b += cl[x as usize].1 as u64,
            Token::Match { len, dist } => b += match_cost(len, dist, cl, cd) as u64,
        }
    }
    b + cl[256].1 as u64
}

// размер дерева в битах, пишу во временный райтер и смотрю счётчик
fn tree_bits(ll: &[u8], dl: &[u8], nlit: usize, ndist: usize) -> u64 {
    let mut w = BitWriter::new();
    w.bits((nlit - 257) as u32, 6);
    w.bits((ndist - 1) as u32, 5);
    let mut both = Vec::with_capacity(nlit + ndist);
    both.extend_from_slice(&ll[..nlit]);
    both.extend_from_slice(&dl[..ndist]);
    write_tree(&mut w, &both);
    w.total
}

// цена токенов через fixed таблицу, без заголовка
fn fixed_bits(toks: &[Token]) -> u64 {
    let mut b = 0u64;
    for t in toks {
        match *t {
            Token::Lit(x) => b += fixed_litlen(x as usize).1 as u64,
            Token::Match { len, dist } => {
                let (lc, le, _) = len_ev(len);
                let (dc, de, _) = dist_ev(dist);
                b += fixed_litlen(lc as usize).1 as u64 + le as u64
                    + fixed_dist(dc as usize).1 as u64 + de as u64;
            }
        }
    }
    b + fixed_litlen(256).1 as u64
}

// пишу токены fixed кодами
fn write_fixed(w: &mut BitWriter, toks: &[Token]) {
    for t in toks {
        match *t {
            Token::Lit(b) => { let (c, l) = fixed_litlen(b as usize); w.bits(c, l); }
            Token::Match { len, dist } => {
                let (lc, le, ev) = len_ev(len);
                let (c, l) = fixed_litlen(lc as usize);
                w.bits(c, l);
                if le > 0 { w.bits(ev as u32, le); }
                let (dc, de, evd) = dist_ev(dist);
                let (c2, l2) = fixed_dist(dc as usize);
                w.bits(c2, l2);
                if de > 0 { w.bits(evd, de); }
            }
        }
    }
    let (c, l) = fixed_litlen(256);
    w.bits(c, l);
}
fn write_dynamic(w: &mut BitWriter, toks: &[Token], ll: &[u8], dl: &[u8], nlit: usize, ndist: usize) {
    let cl = canon_codes(ll);
    let cd = canon_codes(dl);
    let mut both = Vec::with_capacity(nlit + ndist);
    both.extend_from_slice(&ll[..nlit]);
    both.extend_from_slice(&dl[..ndist]);
    w.bits((nlit - 257) as u32, 6);
    w.bits((ndist - 1) as u32, 5);
    write_tree(w, &both);
    for t in toks {
        match *t {
            Token::Lit(b) => { let (c, l) = cl[b as usize]; w.bits(c, l); }
            Token::Match { len, dist } => {
                let (lc, le, ev) = len_ev(len);
                let (c, l) = cl[lc as usize];
                w.bits(c, l);
                if le > 0 { w.bits(ev as u32, le); }
                let (dc, de, evd) = dist_ev(dist);
                let (c2, l2) = cd[dc as usize];
                w.bits(c2, l2);
                if de > 0 { w.bits(evd, de); }
            }
        }
    }
    let (c, l) = cl[256];
    w.bits(c, l);
}
fn encode_block(data: &[u8], bs: usize, be: usize, mcached: &[Vec<(usize, usize)>], _is_final: bool) -> (Vec<u8>, u64, bool) {
    // первый проход с плоскими ценами, дальше уточняем
    let flat_l: Vec<(u32, u8)> = (0..NLIT).map(|_| (0, 9)).collect();
    let flat_d: Vec<(u32, u8)> = (0..32).map(|_| (0, 6)).collect();
        // матчи уже посчитаны снаружи, mcached[i-bs] это позиция bs+i
        // проход 1: грубо -> частоты -> деревья
        let t1 = parse_block(data, bs, be, mcached, &flat_l, &flat_d);
        let mut fl = vec![0u64; NLIT];
        let mut fd = vec![0u64; 32];
        tokens_freq(&t1, &mut fl, &mut fd);
        fl[256] += 1;
        let ll = build_lengths(&fl, 15);
        let dl = build_lengths(&fd, 15);
        let cl = canon_codes(&ll);
        let cd = canon_codes(&dl);
        // проход 2: с нормальными ценами
        let toks2 = parse_block(data, bs, be, mcached, &cl, &cd);
        // если уже сошлось с первым, дальше крутить смысла нет
        if toks2 == t1 {
            let (llm, dlm, nlitm, ndistm) = trees_for(&toks2);
            let clm = canon_codes(&llm);
            let cdm = canon_codes(&dlm);
            let dynm = data_bits(&toks2, &clm, &cdm) + tree_bits(&llm, &dlm, nlitm, ndistm);
            let fixm = fixed_bits(&toks2);
            if fixm < dynm {
                let mut w = BitWriter::new();
                write_fixed(&mut w, &toks2);
                let (b, n) = w.finish();
                return (b, n, false);
            } else {
                let mut w = BitWriter::new();
                write_dynamic(&mut w, &toks2, &llm, &dlm, nlitm, ndistm);
                let (b, n) = w.finish();
                return (b, n, true);
            }
        }
        let (llm, dlm, nlitm, ndistm) = trees_for(&toks2);
        let clm = canon_codes(&llm);
        let cdm = canon_codes(&dlm);
        // проход 3: ещё раз с новыми деревьями
        let toks3 = parse_block(data, bs, be, mcached, &clm, &cdm);
        let (ll3, dl3, nlit3, ndist3) = trees_for(&toks3);
        // проход E: цены через -log2 со сглаживанием, иногда находит получше
        // но только если 2 и 3 разошлись, иначе зря время жечь
        let converged = toks3 == toks2;
        // честно считаем все варианты и берём самый дешёвый
        let cl2 = canon_codes(&llm);
        let cd2 = canon_codes(&dlm);
        let dyn2 = data_bits(&toks2, &cl2, &cd2) + tree_bits(&llm, &dlm, nlitm, ndistm);
        let cl3 = canon_codes(&ll3);
        let cd3 = canon_codes(&dl3);
        let dyn3 = data_bits(&toks3, &cl3, &cd3) + tree_bits(&ll3, &dl3, nlit3, ndist3);
        let fix2 = fixed_bits(&toks2);
        let fix3 = fixed_bits(&toks3);
        // E вариант лениво: полный разбор только если он отличается от 2 и 3
        let mut order: Vec<(u64, u8)> = vec![(dyn2, 0), (dyn3, 1), (fix2, 3), (fix3, 4)];
        if !converged {
            let (qe_l, qe_d) = q_tables(&toks3);
            let ql: Vec<(u32, u8)> = qe_l.iter().map(|&b| (0u32, b)).collect();
            let qd: Vec<(u32, u8)> = qe_d.iter().map(|&b| (0u32, b)).collect();
            let toks_e = parse_block(data, bs, be, mcached, &ql, &qd);
            if toks_e != toks3 && toks_e != toks2 {
                let (ll_e, dl_e, nlit_e, ndist_e) = trees_for(&toks_e);
                let cl_e = canon_codes(&ll_e);
                let cd_e = canon_codes(&dl_e);
                let dyn_e = data_bits(&toks_e, &cl_e, &cd_e) + tree_bits(&ll_e, &dl_e, nlit_e, ndist_e);
                let fix_e = fixed_bits(&toks_e);
                order.push((dyn_e, 2));
                order.push((fix_e, 5));
                order.sort_by_key(|x| x.0);
                // пишем тело блока БЕЗ заголовка (fin+typ добавит сшивка в compress)
                match order[0].1 {
                    0 => {
                        let mut w = BitWriter::new();
                        write_dynamic(&mut w, &toks2, &llm, &dlm, nlitm, ndistm);
                        let (b, n) = w.finish();
                        return (b, n, true);
                    }
                    1 => {
                        let mut w = BitWriter::new();
                        write_dynamic(&mut w, &toks3, &ll3, &dl3, nlit3, ndist3);
                        let (b, n) = w.finish();
                        return (b, n, true);
                    }
                    2 => {
                        let mut w = BitWriter::new();
                        write_dynamic(&mut w, &toks_e, &ll_e, &dl_e, nlit_e, ndist_e);
                        let (b, n) = w.finish();
                        return (b, n, true);
                    }
                    3 => {
                        let mut w = BitWriter::new();
                        write_fixed(&mut w, &toks2);
                        let (b, n) = w.finish();
                        return (b, n, false);
                    }
                    4 => {
                        let mut w = BitWriter::new();
                        write_fixed(&mut w, &toks3);
                        let (b, n) = w.finish();
                        return (b, n, false);
                    }
                    _ => {
                        let mut w = BitWriter::new();
                        write_fixed(&mut w, &toks_e);
                        let (b, n) = w.finish();
                        return (b, n, false);
                    }
                }
            }
        }
        order.sort_by_key(|x| x.0);
        // тело блока без заголовка, заголовок потом при сшивке допишут
        // (E тут нет: либо сошлось, либо E совпал и уже вернулся выше)
        match order[0].1 {
            0 => {
                let mut w = BitWriter::new();
                write_dynamic(&mut w, &toks2, &llm, &dlm, nlitm, ndistm);
                let (b, n) = w.finish();
                (b, n, true)
            }
            1 => {
                let mut w = BitWriter::new();
                write_dynamic(&mut w, &toks3, &ll3, &dl3, nlit3, ndist3);
                let (b, n) = w.finish();
                (b, n, true)
            }
            3 => {
                let mut w = BitWriter::new();
                write_fixed(&mut w, &toks2);
                let (b, n) = w.finish();
                (b, n, false)
            }
            _ => {
                let mut w = BitWriter::new();
                write_fixed(&mut w, &toks3);
                let (b, n) = w.finish();
                (b, n, false)
            }
        }
}

// -log2 цены со сглаживанием, чтоб нулевые частоты не давали бесконечность
fn q_tables(toks: &[Token]) -> (Vec<u8>, Vec<u8>) {
    let (mut fl, mut fd) = (vec![0u64; NLIT], vec![0u64; 32]);
    tokens_freq(toks, &mut fl, &mut fd);
    fl[256] += 1;
    let tl: u64 = fl.iter().sum();
    let td: u64 = fd.iter().sum();
    let ql: Vec<u8> = fl.iter().map(|&f| {
        let p = (f as f64 + 0.3) / (tl as f64 + 0.3 * NLIT as f64);
        (-p.log2()).ceil().max(1.0).min(15.0) as u8
    }).collect();
    let qd: Vec<u8> = fd.iter().map(|&f| {
        let p = (f as f64 + 0.3) / (td as f64 + 0.3 * 32.0);
        (-p.log2()).ceil().max(1.0).min(15.0) as u8
    }).collect();
    (ql, qd)
}

// полная цена куска как отдельного блока, dynamic или fixed, без заголовка
fn pair_cost(toks: &[Token]) -> u64 {
    let (ll, dl, nlit, ndist) = trees_for(toks);
    let cl = canon_codes(&ll);
    let cd = canon_codes(&dl);
    let dyn_c = data_bits(toks, &cl, &cd) + tree_bits(&ll, &dl, nlit, ndist);
    let fix_c = fixed_bits(toks);
    dyn_c.min(fix_c)
}

// режем диапазон токенов пополам пока выгодно, границы в байтах складываем в out
fn split_range(toks: &[Token], off: &[usize], tl: usize, tr: usize, out: &mut Vec<(usize, usize)>, depth: u8) {
    const MIN_PIECE: usize = 2048;
    const GAIN_THRESH: u64 = 512; // меньше нет смысла, шум
    let bytes = off[tr] - off[tl];
    if depth == 0 || tr - tl < 4 || bytes <= MIN_PIECE {
        out.push((off[tl], off[tr]));
        return;
    }
    let base = pair_cost(&toks[tl..tr]);
    let mut best_gain = 0i64;
    let mut best_at = 0usize;
    // пробую 6 сечений равномерно
    for k in 1..=6 {
        let tm = tl + (tr - tl) * k / 7;
        if off[tm] - off[tl] < MIN_PIECE || off[tr] - off[tm] < MIN_PIECE { continue; }
        let c = pair_cost(&toks[tl..tm]) + pair_cost(&toks[tm..tr]) + 3; // +заголовок
        let gain = base as i64 - c as i64;
        if gain > best_gain { best_gain = gain; best_at = tm; }
    }
    if best_gain > GAIN_THRESH as i64 {
        split_range(toks, off, tl, best_at, out, depth - 1);
        split_range(toks, off, best_at, tr, out, depth - 1);
    } else {
        out.push((off[tl], off[tr]));
    }
}

pub fn compress(data: &[u8]) -> Vec<u8> {
    let n = data.len();
    // пустой файл это один пустой dynamic блок, чтоб декодер не парился
    if n == 0 {
        let mut w = BitWriter::new();
        w.bit(1); w.bits(2, 2); // final dynamic
        let mut fl = vec![0u64; NLIT]; fl[256] = 1;
        let mut fd = vec![0u64; 32]; fd[0] = 1;
        let ll = build_lengths(&fl, 15);
        let dl = build_lengths(&fd, 15);
        let nlit = 257; let ndist = 1;
        let mut both = vec![]; both.extend_from_slice(&ll[..nlit]); both.extend_from_slice(&dl[..ndist]);
        w.bits((nlit - 257) as u32, 6); w.bits((ndist - 1) as u32, 5);
        write_tree(&mut w, &both);
        let cl = canon_codes(&ll);
        w.bits(cl[256].0, cl[256].1);
        let (bits, _) = w.finish();
        let mut out = Vec::with_capacity(14 + bits.len());
        out.extend_from_slice(MAGIC);
        out.extend_from_slice(&0u32.to_le_bytes());
        out.extend_from_slice(&crc32(data).to_le_bytes());
        out.extend_from_slice(&bits);
        return out;
    }
    // хеши считаю сразу все, цепочки линкую сортировкой по хешу (быстро, без сравнений байт).
    // сам тяжёлый поиск потом идёт в потоках, prev только читается.
    let nh = if n >= 3 { n - 2 } else { 0 }; // позиций с хешем
    let mut hh = vec![0usize; nh];
    for i in 0..nh { hh[i] = hash3(data, i); }
    // counting sort по хешу, стабильно (внутри бакета позиции по возрастанию)
    let mut cnt = vec![0u32; HASH_SIZE];
    for &h in &hh { cnt[h] += 1; }
    let mut off = vec![0u32; HASH_SIZE + 1];
    for i in 0..HASH_SIZE { off[i + 1] = off[i] + cnt[i]; }
    let mut order = vec![0u32; nh];
    let mut cur = off[..HASH_SIZE].to_vec();
    for (i, &h) in hh.iter().enumerate() {
        order[cur[h] as usize] = i as u32;
        cur[h] += 1;
    }
    // линкую соседей в бакетах: prev[pos] = предыдущая позиция с тем же хешем
    let mut prev = vec![-1i32; n];
    for h in 0..HASH_SIZE {
        let mut last = -1i32;
        for k in off[h]..off[h + 1] {
            let pos = order[k as usize] as usize;
            prev[pos] = last;
            last = pos as i32;
        }
    }
    // тяжёлый поиск матчей — в потоках, у каждого свой кусок позиций.
    // куски не пересекаются, так что через сырой указатель (scope всё равно всех дождётся)
    let ncpu = std::thread::available_parallelism().map(|x| x.get()).unwrap_or(4).min(32);
    let mut cache: Vec<Vec<(usize, usize)>> = (0..n).map(|_| Vec::new()).collect();
    let ptr = cache.as_mut_ptr() as usize; // через usize чтоб Send прошёл, куски не пересекаются
    let pr: &[i32] = &prev;
    std::thread::scope(|s| {
        let chunk = (n + ncpu - 1) / ncpu;
        let mut hs = Vec::new();
        for t in 0..ncpu {
            let lo = t * chunk;
            let hi = ((t + 1) * chunk).min(n);
            if lo >= hi { break; }
            hs.push(s.spawn(move || {
                let cref: &mut [Vec<(usize, usize)>] =
                    unsafe { std::slice::from_raw_parts_mut((ptr as *mut Vec<(usize, usize)>).add(lo), hi - lo) };
                for (j, slot) in cref.iter_mut().enumerate() {
                    let gi = lo + j;
                    if gi + MIN_MATCH <= n && gi < nh {
                        *slot = find_matches_from(data, gi, pr[gi], pr);
                    }
                }
            }));
        }
        for h in hs { h.join().unwrap(); }
    });
    // грубый парсинг плоской моделью, нужен только для границ
    let flat_l: Vec<(u32, u8)> = (0..NLIT).map(|_| (0, 9)).collect();
    let flat_d: Vec<(u32, u8)> = (0..32).map(|_| (0, 6)).collect();
    // режу на куски по 128к максимум, их потом сплит поделит если надо
    const MAX_PIECE: usize = 131072;
    let mut init = Vec::new();
    let mut bs0 = 0;
    while bs0 < n {
        let be0 = (bs0 + MAX_PIECE).min(n);
        init.push((bs0, be0));
        bs0 = be0;
    }
    let mut bounds: Vec<(usize, usize)> = Vec::new();
    for (cs, ce) in init {
        let mc: &[Vec<(usize, usize)>] = &cache[cs..ce];
        let gtoks = parse_block(data, cs, ce, mc, &flat_l, &flat_d);
        // считаю на каком байте каждый токен начинается, для сплита надо
        let mut off = Vec::with_capacity(gtoks.len() + 1);
        off.push(cs);
        for t in &gtoks {
            let l = match *t { Token::Lit(_) => 1, Token::Match { len, .. } => len };
            off.push(off.last().unwrap() + l);
        }
        split_range(&gtoks, &off, 0, gtoks.len(), &mut bounds, 4);
    }
    // сами блоки жмутся в потоках, кэш общий read-only
    let nb = bounds.len();
    let mut chunks: Vec<(Vec<u8>, u64, bool)> = vec![(Vec::new(), 0, true); nb];
    std::thread::scope(|s| {
        let mut hs = Vec::new();
        for &(bs, be) in bounds.iter() {
            let mc: &[Vec<(usize, usize)>] = &cache[bs..be];
            hs.push(s.spawn(move || {
                encode_block(data, bs, be, mc, be == data.len())
            }));
        }
        for (bi, h) in hs.into_iter().enumerate() {
            chunks[bi] = h.join().unwrap();
        }
    });
    // сшиваю чанки по порядку. если dynamic вышел больше чем тупо байты положить, кладу байты
    let mut w = BitWriter::new();
    for (bi, (bs, be)) in bounds.iter().enumerate() {
        let (bytes, nbits, is_dyn) = &chunks[bi];
        let rawlen = be - bs;
        let pos = w.total + 3; // fin+typ займут 3 бита
        let pad = (8 - (pos % 8)) % 8;
        // чанки без заголовка лежат, заголовок fin(1)+typ(2)
        let coded_bits = *nbits + 3;
        // stored режу по 65535, длина u16 же
        let nstored = (rawlen + 0xFFFF - 1) / 0xFFFF.max(1);
        let stored_bits_total = nstored as u64 * 3 + pad as u64 + nstored as u64 * 16 + rawlen as u64 * 8;
        if rawlen > 0 && stored_bits_total < coded_bits {
            let mut off = *bs;
            while off < *be {
                let chunk = (*be - off).min(0xFFFF);
                let last = chunk + off == *be && *be == n;
                w.bit(if last { 1 } else { 0 });
                w.bits(0, 2); // stored = 00
                w.align8();
                w.raw_bytes(&(chunk as u16).to_le_bytes());
                w.raw_bytes(&data[off..off + chunk]);
                off += chunk;
            }
        } else {
            let fin = if *be == n { 1 } else { 0 };
            w.bit(fin);
            w.bits(if *is_dyn { 2 } else { 1 }, 2); // 10 dynamic, 01 fixed
            for k in 0..*nbits {
                let b = (bytes[(k / 8) as usize] >> (7 - (k % 8))) & 1;
                w.bit(b as u32);
            }
        }
    }
    let (bits, _) = w.finish();
    let mut out = Vec::with_capacity(14 + bits.len());
    out.extend_from_slice(MAGIC);
    out.extend_from_slice(&(n as u32).to_le_bytes());
    out.extend_from_slice(&crc32(data).to_le_bytes());
    out.extend_from_slice(&bits);
    out
}

pub fn decompress(blob: &[u8]) -> Result<Vec<u8>, String> {
    if blob.len() < 14 || &blob[..6] != MAGIC { return Err("not a .scf file (v4)".into()); }
    let orig = u32::from_le_bytes(blob[6..10].try_into().unwrap()) as usize;
    let crc = u32::from_le_bytes(blob[10..14].try_into().unwrap());
    let bits = &blob[14..];
    let nbits = bits.len() as u64 * 8;
    let mut r = BitReader { buf: bits, pos: 0, nbits };
    let mut out: Vec<u8> = Vec::with_capacity(orig);
    loop {
        let fin = r.bit().ok_or("block hdr")?;
        let typ = r.bits(2).ok_or("block type")?;
        if typ == 3 { return Err("bad block type".into()); }
        if typ == 0 {
            // stored: выравнивание + len + данные
            while r.pos % 8 != 0 { r.bit(); }
            let bytepos = (r.pos / 8) as usize;
            if bits.len() < bytepos + 2 { return Err("stored hdr".into()); }
            let ln = u16::from_le_bytes(bits[bytepos..bytepos + 2].try_into().unwrap()) as usize;
            r.pos += 16;
            let bytepos = (r.pos / 8) as usize;
            if bits.len() < bytepos + ln { return Err("stored data".into()); }
            out.extend_from_slice(&bits[bytepos..bytepos + ln]);
            r.pos += ln as u64 * 8;
        } else if typ == 2 {
            let (ll, dl) = read_tree(&mut r)?;
            let dlit = Decoder::new(&ll);
            let ddist = Decoder::new(&dl);
            loop {
                let s = dlit.sym(&mut r).ok_or("lit sym")?;
                if s == 256 { break; }
                if s < 256 { out.push(s as u8); }
                else {
                    let li = s - 257;
                    let mut len = LEN_BASE[li] as usize;
                    let e = LEN_EXTRA[li];
                    if e > 0 {
                        let mut v = 0u32;
                        for _ in 0..e { v = (v << 1) | r.bit().ok_or("len extra")?; }
                        len += v as usize;
                    }
                    let ds = ddist.sym(&mut r).ok_or("dist sym")?;
                    let mut dist = DIST_BASE[ds] as usize;
                    let de = DIST_EXTRA[ds];
                    if de > 0 {
                        let mut v = 0u32;
                        for _ in 0..de { v = (v << 1) | r.bit().ok_or("dist extra")?; }
                        dist += v as usize;
                    }
                    if dist == 0 || dist > out.len() { return Err(format!("bad distance {dist} at {}", out.len())); }
                    for _ in 0..len {
                        let b = out[out.len() - dist];
                        out.push(b);
                    }
                }
            }
        }
        if typ == 1 {
            // fixed, коды точные (таблица неканоническая, через длины не восстановить)
            let lc: Vec<(u32, u8)> = (0..NLIT).map(fixed_litlen).collect();
            let dc: Vec<(u32, u8)> = (0..32).map(fixed_dist).collect();
            let dlit = Decoder::from_codes(&lc);
            let ddist = Decoder::from_codes(&dc);
            loop {
                let s = dlit.sym(&mut r).ok_or("lit sym")?;
                if s == 256 { break; }
                if s < 256 { out.push(s as u8); }
                else {
                    let li = s - 257;
                    let mut len = LEN_BASE[li] as usize;
                    let e = LEN_EXTRA[li];
                    if e > 0 {
                        let mut v = 0u32;
                        for _ in 0..e { v = (v << 1) | r.bit().ok_or("len extra")?; }
                        len += v as usize;
                    }
                    let ds = ddist.sym(&mut r).ok_or("dist sym")?;
                    let mut dist = DIST_BASE[ds] as usize;
                    let de = DIST_EXTRA[ds];
                    if de > 0 {
                        let mut v = 0u32;
                        for _ in 0..de { v = (v << 1) | r.bit().ok_or("dist extra")?; }
                        dist += v as usize;
                    }
                    if dist == 0 || dist > out.len() { return Err(format!("bad distance {dist} at {}", out.len())); }
                    for _ in 0..len {
                        let b = out[out.len() - dist];
                        out.push(b);
                    }
                }
            }
        }
        if fin == 1 { break; }
    }
    if out.len() != orig { return Err(format!("size mismatch {} != {orig}", out.len())); }
    if crc32(&out) != crc { return Err("CRC mismatch".into()); }
    Ok(out)
}

// паковка папки в один блоб: SCUFFDIR1 + u32 кол-во + записи
// запись: тип(1б: 0 файл, 1 папка) + len пути u16 + путь + [len данных u64 + данные]
const DIR_MAGIC: &[u8; 9] = b"SCUFFDIR1";

fn pack_dir(root: &std::path::Path) -> Result<Vec<u8>, String> {
    // собираю все пути, сортирую чтоб детерминировано было
    let mut paths: Vec<std::path::PathBuf> = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(p) = stack.pop() {
        let md = std::fs::symlink_metadata(&p).map_err(|e| format!("stat {}: {e}", p.display()))?;
        if md.is_symlink() { continue; } // симлинки не тащу
        if md.is_dir() {
            let mut kids: Vec<std::path::PathBuf> = std::fs::read_dir(&p)
                .map_err(|e| format!("readdir {}: {e}", p.display()))?
                .filter_map(|e| e.ok().map(|x| x.path()))
                .collect();
            kids.sort();
            for k in kids.into_iter().rev() { stack.push(k); }
            // саму папку тоже кладу (кроме корня), чтоб пустые не терялись
            if p != root { paths.push(p); }
        } else if md.is_file() {
            paths.push(p);
        }
    }
    paths.sort();
    let mut out = Vec::new();
    out.extend_from_slice(DIR_MAGIC);
    out.extend_from_slice(&(paths.len() as u32).to_le_bytes());
    for p in &paths {
        let rel = p.strip_prefix(root).map_err(|_| "bad prefix".to_string())?;
        let rels = rel.to_string_lossy().replace('\\', "/");
        let rb = rels.as_bytes();
        if rb.len() > 0xFFFF { return Err(format!("too long path: {}", rels)); }
        let is_dir = p.is_dir();
        out.push(if is_dir { 1 } else { 0 });
        out.extend_from_slice(&(rb.len() as u16).to_le_bytes());
        out.extend_from_slice(rb);
        if !is_dir {
            let d = std::fs::read(p).map_err(|e| format!("read {}: {e}", p.display()))?;
            out.extend_from_slice(&(d.len() as u64).to_le_bytes());
            out.extend_from_slice(&d);
        }
    }
    Ok(out)
}

fn unpack_dir(blob: &[u8], dst: &std::path::Path) -> Result<usize, String> {
    let mut p = 0;
    if blob.len() < 13 || &blob[..9] != DIR_MAGIC { return Err("not a dir pack".into()); }
    p += 9;
    let n = u32::from_le_bytes(blob[p..p + 4].try_into().unwrap()) as usize;
    p += 4;
    for _ in 0..n {
        if p + 3 > blob.len() { return Err("truncated dir pack".into()); }
        let typ = blob[p];
        p += 1;
        let rl = u16::from_le_bytes(blob[p..p + 2].try_into().unwrap()) as usize;
        p += 2;
        if p + rl > blob.len() { return Err("truncated dir pack".into()); }
        let rel = std::str::from_utf8(&blob[p..p + rl]).map_err(|_| "bad path utf8".to_string())?;
        p += rl;
        // чтоб .. не вылезли наружу
        let target = dst.join(rel);
        if !target.starts_with(dst) { return Err(format!("evil path: {rel}")); }
        if typ == 1 {
            std::fs::create_dir_all(&target).map_err(|e| format!("mkdir {}: {e}", target.display()))?;
        } else if typ == 0 {
            if blob.len() < p + 8 { return Err("truncated dir pack".into()); }
            let ln = u64::from_le_bytes(blob[p..p + 8].try_into().unwrap()) as usize;
            p += 8;
            if blob.len() < p + ln { return Err("truncated dir pack".into()); }
            if let Some(par) = target.parent() {
                std::fs::create_dir_all(par).map_err(|e| format!("mkdir {}: {e}", par.display()))?;
            }
            std::fs::write(&target, &blob[p..p + ln]).map_err(|e| format!("write {}: {e}", target.display()))?;
            p += ln;
        } else {
            return Err("bad entry type".into());
        }
    }
    Ok(n)
}

fn is_dir_pack(blob: &[u8]) -> bool {
    blob.len() >= 9 && &blob[..9] == DIR_MAGIC
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 3 || (a[1] != "c" && a[1] != "d") {
        eprintln!("usage: scuff <c|d> <src> [dst]  (src может быть папкой)");
        std::process::exit(1);
    }
    let t0 = std::time::Instant::now();
    if a[1] == "c" {
        let src = std::path::Path::new(&a[2]);
        // папку сначала пакую в блоб, дальше всё одинаково
        let d = if src.is_dir() {
            pack_dir(src).unwrap_or_else(|e| { eprintln!("error: {e}"); std::process::exit(1); })
        } else {
            std::fs::read(src).unwrap_or_else(|_| { eprintln!("error: не открылся {}", a[2]); std::process::exit(1); })
        };
        let c = compress(&d);
        let dst = if a.len() > 3 { a[3].clone() } else { format!("{}.scf", a[2]) };
        std::fs::write(&dst, &c).unwrap();
        println!("SCUFF compressed {} ({}B) -> {} ({}B) {:.2}% in {:.2?}",
            a[2], d.len(), dst, c.len(), 100.0 * c.len() as f64 / d.len().max(1) as f64, t0.elapsed());
    } else {
        let b = std::fs::read(&a[2]).unwrap();
        let d = decompress(&b).unwrap_or_else(|e| { eprintln!("error: {e}"); std::process::exit(1); });
        // если внутри паковка папки, распаковываю в папку
        if is_dir_pack(&d) {
            let dst = if a.len() > 3 { a[3].clone() } else if a[2].ends_with(".scf") { a[2][..a[2].len()-4].to_string() } else { format!("{}_dir", a[2]) };
            let n = unpack_dir(&d, std::path::Path::new(&dst)).unwrap_or_else(|e| { eprintln!("error: {e}"); std::process::exit(1); });
            println!("SCUFF unpacked dir {} ({} entries) in {:.2?}", dst, n, t0.elapsed());
        } else {
            let dst = if a.len() > 3 { a[3].clone() } else if a[2].ends_with(".scf") { a[2][..a[2].len()-4].to_string() } else { format!("{}.out", a[2]) };
            std::fs::write(&dst, &d).unwrap();
            println!("SCUFF decompressed {} -> {} ({}B) in {:.2?}", a[2], dst, d.len(), t0.elapsed());
        }
    }
}

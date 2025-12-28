import React, { useState, useRef, useEffect, useCallback, useMemo } from 'react';
// 新增引入 Image as ImageIcon 以避免名稱衝突
import { Upload, Move, RefreshCw, ChevronUp, ChevronDown, ChevronLeft, ChevronRight, Ruler, ArrowLeft, ArrowRight, Loader2, Minus, Plus, Maximize2, Minimize2, MousePointerClick, Download, Save, FileJson, FileImage, Image as ImageIcon, Wand2 } from 'lucide-react';

// 改為最小目標寬度，不再是固定寬度
const MIN_TARGET_WIDTH = 1000; 
// 為了瀏覽器效能，設定一個合理的上限 (4K解析度寬度)
const MAX_TARGET_WIDTH = 4096;
// 顯示用的基礎寬度限制
const BASE_TARGET_WIDTH = 1000;

const MAGNIFIER_SIZE = 225; 

// --- 輔助函數: 圖片載入 ---
const loadImage = (src) => {
    return new Promise((resolve, reject) => {
        const img = new Image();
        img.crossOrigin = "anonymous"; 
        img.onload = () => resolve(img);
        img.onerror = (e) => reject(new Error("圖片載入失敗，請確認檔案格式是否正確。"));
        img.src = src;
    });
};

// --- 核心函數: 矩陣運算工具 (Matrix Utility) ---
const Matrix = {
    // 矩陣乘法 (A * B)
    multiply: (A, B) => {
        const rowsA = A.length, colsA = A[0].length;
        const rowsB = B.length, colsB = B[0].length;

        if (colsA !== rowsB) throw new Error("矩陣尺寸不匹配");
        
        const C = Array(rowsA).fill(0).map(() => Array(colsB).fill(0));
        
        for (let i = 0; i < rowsA; i++) {
            for (let j = 0; j < colsB; j++) {
                let sum = 0;
                for (let k = 0; k < colsA; k++) {
                    sum += A[i][k] * B[k][j];
                }
                C[i][j] = sum;
            }
        }
        return C;
    },

    // 矩陣求逆
    inverse3x3: (M) => {
        const [a, b, c, d, e, f, g, h, i] = [
            M[0][0], M[0][1], M[0][2],
            M[1][0], M[1][1], M[1][2],
            M[2][0], M[2][1], M[2][2]
        ];

        const det = a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g);
        if (Math.abs(det) < 1e-6) return null;
        const invDet = 1 / det;

        return [
            [(e * i - f * h) * invDet, (c * h - b * i) * invDet, (b * f - c * e) * invDet],
            [(f * g - d * i) * invDet, (a * i - c * g) * invDet, (c * d - a * f) * invDet],
            [(d * h - e * g - 0) * invDet, (b * g - a * h) * invDet, (a * e - b * d) * invDet]
        ];
    },
    
    // 求解 Ax=B 的線性系統
    solveLinearSystem: (A, B) => {
        const n = A.length;
        const M = A.map((row, i) => [...row, B[i]]);

        for (let k = 0; k < n; k++) {
            let i_max = k;
            let v_max = M[k][k];
            for (let i = k + 1; i < n; i++) {
                if (Math.abs(M[i][k]) > Math.abs(v_max)) {
                    v_max = M[i][k];
                    i_max = i;
                }
            }
            if (M[i_max][k] === 0) throw new Error("線性系統奇異");
            
            [M[k], M[i_max]] = [M[i_max], M[k]];

            for (let i = k + 1; i < n; i++) {
                const f = M[i][k] / M[k][k];
                for (let j = k; j < n + 1; j++) {
                    M[i][j] = M[i][j] - M[k][j] * f;
                }
            }
        }

        const X = Array(n).fill(0); 
        for (let i = n - 1; i >= 0; i--) {
            let sum = 0;
            for (let j = i + 1; j < n; j++) sum += M[i][j] * X[j];
            X[i] = (M[i][n] - sum) / M[i][i]; 
        }
        return X;
    }
};

// --- 核心函數: 雙線性插值 ---
const bilinearInterpolation = (imageData, x, y) => {
    const { width, height, data } = imageData;
    const x1 = Math.floor(x), y1 = Math.floor(y);
    const x2 = Math.ceil(x), y2 = Math.ceil(y);

    if (x1 < 0 || x2 >= width || y1 < 0 || y2 >= height) return [0, 0, 0, 255]; 

    const fx = x - x1, fy = y - y1;
    const fx1 = 1 - fx, fy1 = 1 - fy;

    const getPixelIndex = (px, py) => (py * width + px) * 4;
    let r = 0, g = 0, b = 0, a = 0;
    
    // Helper for interpolation
    const interpolate = (idx, w) => {
        r += data[idx] * w; g += data[idx + 1] * w; b += data[idx + 2] * w; a += data[idx + 3] * w;
    }
    
    interpolate(getPixelIndex(x1, y1), fx1 * fy1);
    interpolate(getPixelIndex(x2, y1), fx * fy1);
    interpolate(getPixelIndex(x1, y2), fx1 * fy);
    interpolate(getPixelIndex(x2, y2), fx * fy);

    return [Math.round(r), Math.round(g), Math.round(b), Math.round(a)];
};

// --- 放大鏡組件 (Magnifier Component) ---
const Magnifier = React.memo(({ magnifierState, zoom, cardImage }) => { 
    const { visible, targetX, targetY, imgRect, currentStep, cropPoints, measureLines } = magnifierState;
    const canvasRef = useRef(null);
    
    // 動態計算放大鏡尺寸
    const size = useMemo(() => {
        if (zoom >= 3) return MAGNIFIER_SIZE * 2;   
        if (zoom >= 2) return MAGNIFIER_SIZE * 1.5; 
        return MAGNIFIER_SIZE;                      
    }, [zoom]);

    const halfSize = size / 2;

    useEffect(() => {
        if (!visible || !canvasRef.current || !cardImage || !imgRect || imgRect.width === 0) return;

        const canvas = canvasRef.current;
        const ctx = canvas.getContext('2d');
        
        canvas.width = size;
        canvas.height = size;
        
        const img = cardImage;
        if (!img.complete) return; 

        // 1. 繪製放大後的圖像 (修正邊緣空白問題)
        
        // 填充背景色 (黑色)，避免邊緣透明
        ctx.fillStyle = '#000000';
        ctx.fillRect(0, 0, size, size);

        const imgW = img.naturalWidth;
        const imgH = img.naturalHeight;
        
        // 計算游標相對於圖片左上角的位移 (螢幕像素)
        const relativeX = targetX - imgRect.left;
        const relativeY = targetY - imgRect.top;
        
        // 轉換為 0-1 比例
        const normX = relativeX / imgRect.width;
        const normY = relativeY / imgRect.height;
        
        // 轉換為原圖像素座標
        const srcCenterX = normX * imgW;
        const srcCenterY = normY * imgH;
        
        // 計算在原圖上需要裁切的寬高
        const srcClipW = size / zoom;
        const srcClipH = size / zoom;
        
        // 計算原圖裁切的左上角 (未修正)
        let srcX = srcCenterX - srcClipW / 2;
        let srcY = srcCenterY - srcClipH / 2;
        
        // 目標畫布的繪製位置 (預設是 0,0 填滿整個 canvas)
        let dstX = 0;
        let dstY = 0;
        let dstW = size;
        let dstH = size;

        // *** 關鍵修復：手動計算裁切 (Clipping) ***
        // 避免 drawImage 讀取負值或超出範圍，導致某些瀏覽器渲染錯誤
        
        // 左邊界處理
        if (srcX < 0) {
            dstX = (-srcX) * zoom; // 目標向右移
            dstW -= dstX;          // 寬度減少
            srcX = 0;              // 來源從 0 開始
        }
        // 上邊界處理
        if (srcY < 0) {
            dstY = (-srcY) * zoom; // 目標向下移
            dstH -= dstY;          // 高度減少
            srcY = 0;              // 來源從 0 開始
        }
        // 右邊界處理
        if (srcX + srcClipW > imgW) {
            // 計算超出多少原圖像素
            const overflowX = (srcX + srcClipW) - imgW;
            // 減少目標繪製寬度 (超出部分不畫，保持黑色背景)
            dstW -= overflowX * zoom; 
        }
        // 下邊界處理
        if (srcY + srcClipH > imgH) {
            const overflowY = (srcY + srcClipH) - imgH;
            dstH -= overflowY * zoom;
        }

        // 只有當還有可繪製區域時才繪製
        if (dstW > 0 && dstH > 0) {
            try {
                // 從原圖 (srcX, srcY) 切下 (dstW/zoom, dstH/zoom) 大小
                // 畫到畫布 (dstX, dstY) 大小為 (dstW, dstH)
                ctx.drawImage(
                    img, 
                    srcX, srcY, dstW / zoom, dstH / zoom, 
                    dstX, dstY, dstW, dstH
                );
            } catch (e) {
                console.error("Magnifier draw error:", e);
            }
        }
        
        // 2. 繪製線條與點位
        // 重新計算 scale，因為上面的 drawImage 是基於真實像素的
        const scale = size / (size / zoom); // 其實就是 zoom
        
        // 為了讓線條跟隨圖片，我們需要計算 canvas 中心點對應的原圖座標
        // 這裡回頭使用原始的 srcCenterX, srcCenterY 比較直觀
        
        // 原圖座標 (px) -> Canvas 座標 (px) 的轉換函數
        // CanvasX = (ImgX - SrcCenterX) * Zoom + HalfSize
        const transformX = (x_px) => (x_px - srcCenterX) * zoom + halfSize;
        const transformY = (y_px) => (y_px - srcCenterY) * zoom + halfSize;
        
        ctx.lineWidth = 2;
        ctx.setLineDash([5, 5]); 

        if (currentStep === 'crop' && cropPoints && cropPoints.length === 4) {
            // 裁切框
            ctx.strokeStyle = 'rgba(34, 197, 94, 1)'; 
            ctx.beginPath();
            
            const points = cropPoints.map(p => ({
                x: transformX(p.x * imgW),
                y: transformY(p.y * imgH)
            }));
            
            ctx.moveTo(points[0].x, points[0].y);
            points.forEach((p, i) => { if (i > 0) ctx.lineTo(p.x, p.y); });
            ctx.lineTo(points[0].x, points[0].y);
            ctx.stroke();

            // 裁切點
            ctx.setLineDash([]);
            points.forEach((p) => {
                ctx.fillStyle = 'rgba(34, 197, 94, 1)'; 
                ctx.beginPath();
                ctx.arc(p.x, p.y, 4, 0, Math.PI * 2); // 固定大小，不隨 zoom 縮放
                ctx.fill();
            });
            ctx.setLineDash([5, 5]);
        } else if (currentStep === 'measure' && measureLines) {
            const ml = measureLines;
            const drawHLine = (pct, color) => {
                const y = transformY((pct / 100) * imgH);
                // 優化：只畫在視窗內的線
                if (y >= 0 && y <= size) {
                    ctx.strokeStyle = color;
                    ctx.beginPath();
                    ctx.moveTo(0, y); ctx.lineTo(size, y);
                    ctx.stroke();
                }
            };
            const drawVLine = (pct, color) => {
                const x = transformX((pct / 100) * imgW);
                if (x >= 0 && x <= size) {
                    ctx.strokeStyle = color;
                    ctx.beginPath();
                    ctx.moveTo(x, 0); ctx.lineTo(x, size);
                    ctx.stroke();
                }
            };

            drawHLine(ml.outerTop, 'rgba(59, 130, 246, 1)');
            drawHLine(ml.outerBottom, 'rgba(59, 130, 246, 1)');
            drawVLine(ml.outerLeft, 'rgba(59, 130, 246, 1)');
            drawVLine(ml.outerRight, 'rgba(59, 130, 246, 1)');
            
            drawHLine(ml.innerTop, 'rgba(239, 68, 68, 1)');
            drawHLine(ml.innerBottom, 'rgba(239, 68, 68, 1)');
            drawVLine(ml.innerLeft, 'rgba(239, 68, 68, 1)');
            drawVLine(ml.innerRight, 'rgba(239, 68, 68, 1)');
        }
        
        // 3. 繪製中心紅點
        ctx.setLineDash([]); 
        ctx.fillStyle = 'rgba(255, 0, 0, 0.8)';
        ctx.beginPath();
        ctx.arc(halfSize, halfSize, 3, 0, Math.PI * 2);
        ctx.fill();

    }, [visible, targetX, targetY, imgRect, cardImage, size, zoom, currentStep, cropPoints, measureLines]);

    if (!visible || !imgRect || imgRect.width === 0) return null;

    const finalLeft = targetX - halfSize;
    const finalTop = targetY - halfSize;

    const style = {
        left: `${finalLeft}px`, top: `${finalTop}px`, width: `${size}px`, height: `${size}px`,
    };

    return (
        <div className="fixed rounded-full shadow-2xl z-[100] border-4 border-yellow-400 backdrop-blur-sm transition-opacity duration-150 overflow-hidden bg-gray-900/50" style={style}>
            <canvas ref={canvasRef} className="rounded-full w-full h-full"></canvas>
        </div>
    );
});


function CardGraderTool() {
  const [step, setStep] = useState('upload'); 
  const [originalImage, setOriginalImage] = useState(null); 
  const [originalFileName, setOriginalFileName] = useState("card"); 
  const [processedImage, setProcessedImage] = useState(null); 
  const [isProcessing, setIsProcessing] = useState(false);
  const [zoomLevel, setZoomLevel] = useState(1.0); 
  const [loadingText, setLoadingText] = useState("正在進行透視校正 (Homography)...");
  const [pendingProjectData, setPendingProjectData] = useState(null);
  const [isMagnifierPanelCollapsed, setIsMagnifierPanelCollapsed] = useState(false);

  const [originalCardDims, setOriginalCardDims] = useState({ w: 0, h: 0 }); 
  const [cropPoints, setCropPoints] = useState([]); 
  const [activePointIndex, setActivePointIndex] = useState(null);
  const [lastActivePointIndex, setLastActivePointIndex] = useState(null);

  // 用於空白處檢查的狀態
  const [isGeneralDragging, setIsGeneralDragging] = useState(false);
  // 用於長按偵測
  const longPressTimerRef = useRef(null);

  const [measureLines, setMeasureLines] = useState({
    outerTop: 2, innerTop: 12, outerBottom: 98, innerBottom: 88,
    outerLeft: 3, innerLeft: 13, outerRight: 97, innerRight: 87
  });
  
  const measureLinesRef = useRef(measureLines);
  useEffect(() => { measureLinesRef.current = measureLines; }, [measureLines]);

  const [selectedLineId, setSelectedLineId] = useState(null); 
  const [draggingLineId, setDraggingLineId] = useState(null); 
  const [lastInteractionCoords, setLastInteractionCoords] = useState({});
  const currentMousePosRef = useRef({ clientX: 0, clientY: 0 });

  const [magnifier, setMagnifier] = useState({ 
      visible: false, targetX: 0, targetY: 0, imgRect: null, 
      currentStep: 'upload', cropPoints: [], measureLines: {}, isTrackingMouse: false
  }); 

  const containerRef = useRef(null);
  const imgRef = useRef(null);
  const magnifierTimeoutRef = useRef(null); 

  const cardImageForMagnifier = useMemo(() => {
    if (step === 'crop' && originalImage) return originalImage; 
    if (step === 'measure' && processedImage) return processedImage;
    return null;
  }, [step, originalImage, processedImage]);

  const zoomOptions = [0.2, 0.5, 1.0, 1.5, 2, 3, 5];

  // ... (保留 loadImage, Matrix, bilinearInterpolation, handleReset, JSON handlers 等不變代碼) ...
  // 為節省篇幅，這部分與上一版相同，重點在下面的事件處理修改

  // --- Helper: Get Live Image Rect ---
  const getLiveImageRect = useCallback(() => {
    if (!imgRef.current) return null;
    return imgRef.current.getBoundingClientRect();
  }, []);

  // --- Helper: Show Fixed Magnifier ---
  const showFixedMagnifierAt = useCallback((clientX, clientY) => {
    const imgRect = getLiveImageRect(); 
    if (!imgRect || imgRect.width === 0) return;

    if (magnifierTimeoutRef.current) {
        clearTimeout(magnifierTimeoutRef.current);
        magnifierTimeoutRef.current = null;
    }
    
    setMagnifier(prev => ({
        ...prev, visible: true, isTrackingMouse: false, 
        targetX: clientX, targetY: clientY, imgRect: imgRect,
        currentStep: step, cropPoints: cropPoints, measureLines: measureLinesRef.current, 
    }));

    magnifierTimeoutRef.current = setTimeout(() => {
        setMagnifier(prev => ({ ...prev, visible: false, isTrackingMouse: false }));
        magnifierTimeoutRef.current = null;
    }, 2000); 
  }, [step, cropPoints, measureLinesRef, getLiveImageRect]); 

  // --- Helper: Get Screen Coordinates ---
  const getLineScreenCenter = useCallback((lineId) => {
    if (!lineId || !processedImage) return null;
    const imgRect = getLiveImageRect(); 
    if (!imgRect || imgRect.width === 0) return null;

    const storedCoords = lastInteractionCoords[lineId];
    if (storedCoords) return storedCoords;

    const isH = lineId.includes('Top') || lineId.includes('Bottom');
    const lineVal = measureLinesRef.current[lineId] / 100; 

    let screenX, screenY;
    if (isH) {
        screenX = imgRect.left + imgRect.width / 2;
        screenY = imgRect.top + imgRect.height * lineVal;
    } else {
        screenX = imgRect.left + imgRect.width * lineVal;
        screenY = imgRect.top + imgRect.height / 2;
    }
    return { x: screenX, y: screenY };
  }, [processedImage, lastInteractionCoords, measureLinesRef, getLiveImageRect]);

  // --- Handlers: Upload, JSON, Reset ---
  // (這裡省略重複代碼，與上一版相同) ...
  // 重新貼上這部分以確保完整性
  const handleReset = () => {
      setStep('upload'); setOriginalImage(null); setProcessedImage(null); setPendingProjectData(null);
      setOriginalFileName("card"); setZoomLevel(1.0); setLastActivePointIndex(null);
      setSelectedLineId(null); setDraggingLineId(null); setIsGeneralDragging(false);
      setMeasureLines({ outerTop: 2, innerTop: 12, outerBottom: 98, innerBottom: 88, outerLeft: 3, innerLeft: 13, outerRight: 97, innerRight: 87 });
  };
  const handleJsonUpload = (e) => {
      const file = e.target.files[0]; if (!file) return;
      const reader = new FileReader();
      reader.onload = (event) => {
          try { const data = JSON.parse(event.target.result); if (data && data.cropPoints) setPendingProjectData(data); else alert("錯誤JSON"); } catch (err) { alert("讀取失敗"); }
      }; reader.readAsText(file); e.target.value = '';
  };
  const handleExportJSON = () => {
      if (!originalImage) return;
      const data = { version: "1.0", timestamp: Date.now(), imageName: originalFileName, cropPoints: cropPoints, measureLines: measureLines, results: calculateResults() };
      const blob = new Blob([JSON.stringify(data, null, 2)], { type: "application/json" });
      const url = URL.createObjectURL(blob); const link = document.createElement('a');
      link.download = `${originalFileName.replace(/\.[^/.]+$/, "")}_grading.json`; link.href = url; link.click(); URL.revokeObjectURL(url);
  };
  const handleImageUpload = async (e) => {
    const file = e.target.files[0]; if (!file) return;
    const isHeic = file.type === "image/heic" || file.type === "image/heif" || file.name.toLowerCase().endsWith(".heic");
    if (isHeic) {
        setLoadingText("正在將 HEIC 格式轉換為 JPG..."); setIsProcessing(true);
        try {
            const heic2any = (await import('https://cdn.skypack.dev/heic2any')).default;
            const blob = await heic2any({ blob: file, toType: "image/jpeg", quality: 0.8 });
            const converted = new File([Array.isArray(blob)?blob[0]:blob], file.name.replace(/\.(heic|heif)$/i, ".jpg"), { type: "image/jpeg" });
            processImageFile(converted);
        } catch (e) { alert("HEIC 轉換失敗"); setIsProcessing(false); }
    } else { processImageFile(file); }
    e.target.value = '';
  };
  const processImageFile = (file) => {
      setOriginalFileName(file.name); const reader = new FileReader();
      reader.onload = (event) => {
        const img = new Image(); img.crossOrigin = "anonymous";
        img.onload = () => {
          setOriginalImage(img); setOriginalCardDims({ w: img.naturalWidth, h: img.naturalHeight });
          if (pendingProjectData) { setCropPoints(pendingProjectData.cropPoints); setMeasureLines(pendingProjectData.measureLines); setPendingProjectData(null); setProcessedImage(null); setStep('crop'); }
          else { setCropPoints([{ x: 0.15, y: 0.15 }, { x: 0.85, y: 0.15 }, { x: 0.85, y: 0.85 }, { x: 0.15, y: 0.85 }]); setProcessedImage(null); setStep('crop'); }
          setLastActivePointIndex(null); setIsProcessing(false);
        }; img.src = event.target.result;
      }; reader.readAsDataURL(file);
  };
  const getScreenCoords = useCallback((normX, normY) => {
    const imgRect = getLiveImageRect(); if (!imgRect || imgRect.width === 0) return { x: -100, y: -100 };
    return { x: normX * imgRect.width + imgRect.left, y: normY * imgRect.height + imgRect.top, renderW: imgRect.width, renderH: imgRect.height, offsetX: imgRect.left, offsetY: imgRect.top };
  }, [getLiveImageRect]);

  const handleCropDragStart = (index, e) => {
    e.preventDefault(); e.stopPropagation(); setActivePointIndex(index); setLastActivePointIndex(index); setSelectedLineId(null);
    if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
  };
  const handleLineDragStart = (id, e) => {
    e.stopPropagation(); setSelectedLineId(id); setDraggingLineId(id); setActivePointIndex(null);
    const clientX = e.touches ? e.touches[0].clientX : e.clientX;
    const clientY = e.touches ? e.touches[0].clientY : e.clientY;
    showFixedMagnifierAt(clientX, clientY);
    setLastInteractionCoords(prev => ({ ...prev, [id]: { x: clientX, y: clientY } }));
  };

  // --- 改良版: 空白處互動 (Mobile: Long Press / Desktop: Click) ---
  const handleGeneralMouseDown = (e) => {
      // 電腦版: 點擊即觸發
      setIsGeneralDragging(true);
      const clientX = e.clientX;
      const clientY = e.clientY;
      updateMagnifierForGeneralDrag(clientX, clientY);
  };

  const handleGeneralTouchStart = (e) => {
      // 手機版: 啟動長按計時器
      const touch = e.touches[0];
      const startX = touch.clientX;
      const startY = touch.clientY;
      
      longPressTimerRef.current = setTimeout(() => {
          // 長按觸發：開啟放大鏡模式，並震動回饋
          setIsGeneralDragging(true);
          updateMagnifierForGeneralDrag(startX, startY);
          if (navigator.vibrate) navigator.vibrate(50);
      }, 500); // 500ms 長按
  };

  const updateMagnifierForGeneralDrag = (clientX, clientY) => {
      const imgRect = getLiveImageRect();
      if(imgRect) {
           if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
           setMagnifier(prev => ({ 
              ...prev, visible: true, isTrackingMouse: true, 
              targetX: clientX, targetY: clientY, imgRect: imgRect,
              measureLines: measureLinesRef.current, currentStep: step,
          }));
      }
  }

  // Shared move handler
  const handleGlobalMove = useCallback((e) => {
    // 檢查是否正在進行長按後的移動
    if (longPressTimerRef.current && e.touches) {
        // 如果在長按判定期間移動了，就取消長按（視為捲動頁面）
        clearTimeout(longPressTimerRef.current);
        longPressTimerRef.current = null;
    }

    if (!containerRef.current) return;
    const clientX = e.touches ? e.touches[0].clientX : e.clientX;
    const clientY = e.touches ? e.touches[0].clientY : e.clientY;
    currentMousePosRef.current = { clientX, clientY };

    const imgRect = getLiveImageRect(); 
    if (!imgRect || imgRect.width === 0) return; 

    // Calculate normalized coords for logic
    const relativeX = clientX - imgRect.left;
    const relativeY = clientY - imgRect.top;
    let normX = Math.max(0, Math.min(1, relativeX / imgRect.width));
    let normY = Math.max(0, Math.min(1, relativeY / imgRect.height));

    if (step === 'crop' && activePointIndex !== null) {
      if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
      const nextCropPoints = [...cropPoints];
      nextCropPoints[activePointIndex] = { x: normX, y: normY };
      setCropPoints(nextCropPoints);
       setMagnifier(prev => ({ ...prev, visible: true, isTrackingMouse: true, targetX: clientX, targetY: clientY, imgRect: imgRect, currentStep: step, cropPoints: nextCropPoints }));

    } else if (step === 'measure' && draggingLineId) { 
       if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
       const valPct = (draggingLineId.includes('Left') || draggingLineId.includes('Right')) ? normX * 100 : normY * 100;
       setMeasureLines(prev => ({ ...prev, [draggingLineId]: valPct }));
       setMagnifier(prev => ({ ...prev, visible: true, isTrackingMouse: true, targetX: clientX, targetY: clientY, imgRect: imgRect, measureLines: measureLinesRef.current, currentStep: step }));
       setLastInteractionCoords(prev => ({ ...prev, [draggingLineId]: { x: clientX, y: clientY } }));

    } else if (step === 'measure' && isGeneralDragging) {
        // 處理一般拖曳 (放大鏡檢查)
        if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
        setMagnifier(prev => ({ ...prev, visible: true, isTrackingMouse: true, targetX: clientX, targetY: clientY, imgRect: imgRect, measureLines: measureLinesRef.current, currentStep: step }));
    }
  }, [step, activePointIndex, draggingLineId, isGeneralDragging, cropPoints, getLiveImageRect, showFixedMagnifierAt]); 

  const handleGlobalUp = useCallback(() => {
    // 清除長按計時器
    if (longPressTimerRef.current) {
        clearTimeout(longPressTimerRef.current);
        longPressTimerRef.current = null;
    }

    const wasDragging = activePointIndex !== null || draggingLineId !== null || isGeneralDragging;
    
    setActivePointIndex(null); 
    setDraggingLineId(null); 
    setIsGeneralDragging(false);
    
    if (wasDragging) {
          setMagnifier(prev => ({ ...prev, visible: false, isTrackingMouse: false }));
          if (magnifierTimeoutRef.current) { clearTimeout(magnifierTimeoutRef.current); magnifierTimeoutRef.current = null; }
    }
  }, [draggingLineId, activePointIndex, isGeneralDragging]); 

  useEffect(() => {
    window.addEventListener('mousemove', handleGlobalMove);
    window.addEventListener('mouseup', handleGlobalUp);
    // 使用 passive: false 以允許在需要時 preventDefault (這裡主要依靠 touch-action css 控制)
    window.addEventListener('touchmove', handleGlobalTouchMove, { passive: false });
    window.addEventListener('touchend', handleGlobalUp);
    return () => {
      window.removeEventListener('mousemove', handleGlobalMove);
      window.removeEventListener('mouseup', handleGlobalUp);
      window.removeEventListener('touchmove', handleGlobalTouchMove);
      window.removeEventListener('touchend', handleGlobalUp);
    };
  }, [handleGlobalMove, handleGlobalUp]);

  const handleGlobalTouchMove = (e) => {
     // 只有在我們明確處理拖曳時，才阻止瀏覽器預設行為 (例如捲動)
     if(activePointIndex !== null || draggingLineId !== null || isGeneralDragging) {
         e.preventDefault(); 
         handleGlobalMove(e);
     }
  };

  // ... (performWarpAndProceed, calculateResults, nudgeLine, nudgeCropPoint, handleZoomChange, cycleZoom, downloadResultImage, renderDraggableLine logic same as before) ...
  // 為了節省長度，這裡直接使用之前的邏輯，關鍵在於 render 區塊的事件綁定
  
  // (Paste performWarpAndProceed here)
  const performWarpAndProceed = useCallback(async () => {
    if (!originalImage || !originalImage.src) return; 
    setLoadingText("正在進行透視校正 (Homography)...");
    setIsProcessing(true);
    try {
        const srcW = originalCardDims.w;
        const srcH = originalCardDims.h;
        const P0 = cropPoints[0], P1 = cropPoints[1], P2 = cropPoints[2], P3 = cropPoints[3];
        const distPx = (pA, pB) => Math.sqrt(Math.pow((pA.x - pB.x) * srcW, 2) + Math.pow((pA.y - pB.y) * srcH, 2));
        const avgSrcW = (distPx(P0, P1) + distPx(P3, P2)) / 2;
        const avgSrcH = (distPx(P0, P3) + distPx(P1, P2)) / 2;
        if (avgSrcH < 1 || avgSrcW < 1) throw new Error("裁剪區域無效。");
        const targetW = Math.max(MIN_TARGET_WIDTH, Math.min(MAX_TARGET_WIDTH, Math.round(avgSrcW)));
        const ratio = avgSrcW / avgSrcH;
        const targetH = Math.round(targetW / ratio);
        const srcPoints = cropPoints.map(p => ([p.x * srcW, p.y * srcH]));
        const dstPoints = [[0, 0], [targetW, 0], [targetW, targetH], [0, targetH]];
        const A = [], B = [];
        for (let i = 0; i < 4; i++) {
            const [x, y] = srcPoints[i], [u, v] = dstPoints[i];
            A.push([x, y, 1, 0, 0, 0, -u * x, -u * y]); B.push(u); A.push([0, 0, 0, x, y, 1, -v * x, -v * y]); B.push(v);
        }
        const solution = Matrix.solveLinearSystem(A, B);
        const H_inv = Matrix.inverse3x3(
            [ (solution.slice(0,3)), (solution.slice(3,6)), (solution.slice(6,8).concat([1])) ].flat().reduce((acc, val, i) => {
                if(i % 3 === 0) acc.push([]); acc[acc.length-1].push(val); return acc;
            }, [])
        );
        if (!H_inv) throw new Error("矩陣奇異");
        const canvas = document.createElement('canvas');
        canvas.width = targetW; canvas.height = targetH;
        const ctx = canvas.getContext('2d');
        const tempImageForCanvas = await loadImage(originalImage.src);
        const tempCanvas = document.createElement('canvas');
        tempCanvas.width = srcW; tempCanvas.height = srcH;
        const tempCtx = tempCanvas.getContext('2d');
        tempCtx.drawImage(tempImageForCanvas, 0, 0, srcW, srcH);
        const srcImageData = tempCtx.getImageData(0, 0, srcW, srcH);
        const dstImageData = ctx.createImageData(targetW, targetH);
        const dstData = dstImageData.data;
        for (let y = 0; y < targetH; y++) {
            for (let x = 0; x < targetW; x++) {
                const target_vector = [[x], [y], [1]];
                const source_homogenous = Matrix.multiply(H_inv, target_vector);
                const wW = source_homogenous[2][0]; 
                const sourceX = source_homogenous[0][0] / wW;
                const sourceY = source_homogenous[1][0] / wW;
                const dstIdx = (y * targetW + x) * 4;
                if (sourceX >= 0 && sourceX < srcW - 1 && sourceY >= 0 && sourceY < srcH - 1) {
                    const [r, g, b, a] = bilinearInterpolation(srcImageData, sourceX, sourceY);
                    dstData[dstIdx] = r; dstData[dstIdx + 1] = g; dstData[dstIdx + 2] = b; dstData[dstIdx + 3] = a;
                } else {
                    dstData[dstIdx] = 0; dstData[dstIdx + 1] = 0; dstData[dstIdx + 2] = 0; dstData[dstIdx + 3] = 255;
                }
            }
        }
        ctx.putImageData(dstImageData, 0, 0);
        const newImg = new Image();
        newImg.onload = () => {
            setProcessedImage(newImg); setIsProcessing(false); setStep('measure');
            setSelectedLineId(null); setLastInteractionCoords({});
            if (containerRef.current) containerRef.current.scrollTop = 0;
        };
        newImg.src = canvas.toDataURL('image/png'); 
    } catch (error) {
        console.error("Homography error:", error);
        setIsProcessing(false);
    }
  }, [originalImage, originalCardDims, cropPoints]);

  const calculateResults = () => {
    const topBorder = Math.abs(measureLines.innerTop - measureLines.outerTop);
    const bottomBorder = Math.abs(measureLines.outerBottom - measureLines.innerBottom);
    const leftBorder = Math.abs(measureLines.innerLeft - measureLines.outerLeft);
    const rightBorder = Math.abs(measureLines.outerRight - measureLines.innerRight);
    const totalV = topBorder + bottomBorder || 1;
    const totalH = leftBorder + rightBorder || 1;
    return {
        v: { top: (topBorder / totalV) * 100, bottom: (bottomBorder / totalV) * 100 },
        h: { left: (leftBorder / totalH) * 100, right: (rightBorder / totalH) * 100 }
    };
  };
  const results = calculateResults();
  const getNudgePixels = (zoom) => { if (zoom >= 5) return 1; if (zoom >= 3) return 2; if (zoom >= 2) return 3; return 5; };
  const nudgeLine = (val) => {
    if (!selectedLineId || !processedImage) return;
    const lineIdToNudge = selectedLineId;
    const imgRect = getLiveImageRect(); 
    if(!imgRect) return;
    const isHLine = lineIdToNudge.includes('Top') || lineIdToNudge.includes('Bottom');
    const pixelSize = isHLine ? processedImage.naturalHeight : processedImage.naturalWidth;
    const pxPct = (1 / pixelSize) * 100;
    const pixels = getNudgePixels(zoomLevel);
    const currentVal = measureLines[lineIdToNudge];
    const newVal = Math.max(0, Math.min(100, currentVal + (val * pixels * pxPct)));
    setMeasureLines(prev => ({ ...prev, [lineIdToNudge]: newVal }));
    let targetX, targetY;
    const lastCoords = lastInteractionCoords[lineIdToNudge];
    if (isHLine) {
        const lastScreenX = lastCoords ? lastCoords.x : (imgRect.left + imgRect.width / 2);
        targetX = Math.max(imgRect.left, Math.min(imgRect.right, lastScreenX));
        targetY = imgRect.top + imgRect.height * (newVal / 100);
    } else {
        const lastScreenY = lastCoords ? lastCoords.y : (imgRect.top + imgRect.height / 2);
        targetX = imgRect.left + imgRect.width * (newVal / 100);
        targetY = Math.max(imgRect.top, Math.min(imgRect.bottom, lastScreenY));
    }
    setLastInteractionCoords(prev => ({ ...prev, [lineIdToNudge]: { x: targetX, y: targetY } }));
    showFixedMagnifierAt(targetX, targetY); 
  };
  const nudgeCropPoint = (dx, dy) => {
      if (lastActivePointIndex === null || !originalCardDims.w) return;
      const rect = imgRef.current?.getBoundingClientRect(); 
      const pixels = getNudgePixels(zoomLevel);
      const normDx = (dx * pixels) / originalCardDims.w;
      const normDy = (dy * pixels) / originalCardDims.h;
      setCropPoints(prev => {
          const newPoints = [...prev]; const pt = newPoints[lastActivePointIndex];
          newPoints[lastActivePointIndex] = { x: Math.max(0, Math.min(1, pt.x + normDx)), y: Math.max(0, Math.min(1, pt.y + normDy)) };
          return newPoints;
      });
      if (rect) {
          const currentPt = cropPoints[lastActivePointIndex];
          const targetX = rect.left + (currentPt.x + normDx) * rect.width;
          const targetY = rect.top + (currentPt.y + normDy) * rect.height;
          showFixedMagnifierAt(targetX, targetY);
      }
  };
  const handleZoomChange = (newZoom) => {
      setZoomLevel(newZoom);
      let targetX, targetY;
      if (step === 'measure' && selectedLineId) {
          const screenCenter = getLineScreenCenter(selectedLineId);
          if (screenCenter) { targetX = screenCenter.x; targetY = screenCenter.y; }
      } else {
          const imgRect = getLiveImageRect();
          if (imgRect) { targetX = imgRect.left + imgRect.width / 2; targetY = imgRect.top + imgRect.height / 2; }
      }
      if (targetX !== undefined) showFixedMagnifierAt(targetX, targetY);
  }
  const cycleZoom = () => {
      const currentIndex = zoomOptions.indexOf(zoomLevel);
      const nextIndex = (currentIndex + 1) % zoomOptions.length;
      handleZoomChange(zoomOptions[nextIndex]);
  };
  const downloadResultImage = async () => {
    if (!processedImage) return;
    const canvas = document.createElement('canvas');
    const ctx = canvas.getContext('2d');
    const w = processedImage.naturalWidth;
    const h = processedImage.naturalHeight;
    const footerHeight = 120;
    canvas.width = w; canvas.height = h + footerHeight;
    ctx.fillStyle = '#111827'; ctx.fillRect(0, 0, w, canvas.height);
    ctx.drawImage(processedImage, 0, 0);
    const drawLine = (pct, isH, color) => {
        ctx.strokeStyle = color; ctx.lineWidth = 3; ctx.setLineDash([10, 10]); ctx.beginPath();
        if (isH) { const y = (pct / 100) * h; ctx.moveTo(0, y); ctx.lineTo(w, y); } else { const x = (pct / 100) * w; ctx.moveTo(x, 0); ctx.lineTo(x, h); }
        ctx.stroke();
    };
    const ml = measureLines;
    drawLine(ml.outerTop, true, '#3b82f6'); drawLine(ml.outerBottom, true, '#3b82f6');
    drawLine(ml.outerLeft, false, '#3b82f6'); drawLine(ml.outerRight, false, '#3b82f6');
    drawLine(ml.innerTop, true, '#ef4444'); drawLine(ml.innerBottom, true, '#ef4444');
    drawLine(ml.innerLeft, false, '#ef4444'); drawLine(ml.innerRight, false, '#ef4444');
    ctx.setLineDash([]); ctx.fillStyle = '#ffffff'; ctx.font = 'bold 32px sans-serif'; ctx.textAlign = 'center';
    const res = calculateResults();
    const textV = `上下比例 (V): ${res.v.top.toFixed(1)} : ${res.v.bottom.toFixed(1)}`;
    const textH = `左右比例 (H): ${res.h.left.toFixed(1)} : ${res.h.right.toFixed(1)}`;
    ctx.fillText(textH, w * 0.25, h + 70); ctx.fillText(textV, w * 0.75, h + 70);
    ctx.strokeStyle = '#374151'; ctx.lineWidth = 2; ctx.beginPath(); ctx.moveTo(w/2, h + 20); ctx.lineTo(w/2, h + 100); ctx.stroke();
    const link = document.createElement('a');
    const baseName = originalFileName.replace(/\.[^/.]+$/, "");
    link.download = `${baseName}_grading.png`; link.href = canvas.toDataURL('image/png'); link.click();
  };
  const renderDraggableLine = (id, orientation, colorClass, isInner) => {
    const val = measureLines[id];
    const isActive = selectedLineId === id; 
    const isHorizontal = orientation === 'horizontal';
    const style = isHorizontal ? { top: `${val}%` } : { left: `${val}%` };
    // Add touch-action: none to prevent browser handling
    const styleWithTouch = { ...style, touchAction: 'none' };
    const cursor = isHorizontal ? 'cursor-row-resize' : 'cursor-col-resize';
    const hitAreaStyle = isHorizontal ? { top: '-10px', bottom: '-10px', left: 0, right: 0 } : { left: '-10px', right: '-10px', top: 0, bottom: 0 };
    const lineClasses = `absolute w-full h-full border border-dashed transition-colors ${isHorizontal ? 'border-t' : 'border-l'}`;

    return (
        <div key={id} className={`absolute z-20 group ${cursor}`} style={{...styleWithTouch, ...(isHorizontal ? {left:0, right:0, height:0} : {top:0, bottom:0, width:0})}}
            onMouseDown={(e) => handleLineDragStart(id, e)} onTouchStart={(e) => handleLineDragStart(id, e)}>
            <div className={`${lineClasses} ${isActive ? 'border-yellow-400 z-50 shadow-[0_0_5px_rgba(255,255,0,0.8)]' : colorClass}`}></div>
            <div className="absolute bg-transparent" style={hitAreaStyle}></div>
            {isActive && <div className={`absolute ${isHorizontal ? 'left-1/2 -top-6 transform -translate-x-1/2' : 'top-1/2 -left-6 transform -translate-y-1/2'} bg-gray-900 text-[10px] text-white px-1 rounded whitespace-nowrap pointer-events-none`}>{isInner ? '紅線 (圖案)' : '藍線 (卡邊)'}</div>}
        </div>
    );
  };
  
  const [coordsKey, setCoordsKey] = useState(0);
  useEffect(() => { setTimeout(() => setCoordsKey(k => k + 1), 50); }, [step]); 
  const handleBackToCrop = () => { setStep('crop'); setSelectedLineId(null); setProcessedImage(null); };
  
  const isImageStep = step === 'crop' || step === 'measure';
  const mainClass = `flex-1 relative w-full overflow-auto select-none p-2 md:p-6 flex justify-center items-start`; 
  
  const activePt = lastActivePointIndex !== null ? cropPoints[lastActivePointIndex] : null;

  return (
    <div className="h-screen bg-gray-950 text-white font-sans flex flex-col overflow-hidden">
      <header className="bg-gray-900 border-b border-gray-800 h-12 flex items-center justify-between px-4 shrink-0 z-50">
        <div className="flex items-center gap-2"><Ruler className="text-blue-400" size={18} /><span className="font-bold text-sm md:text-base bg-gradient-to-r from-blue-400 to-purple-400 bg-clip-text text-transparent">PTCG Grade (v1.0.0)</span></div>
        <div className="flex items-center gap-2 text-xs">{step !== 'upload' && (<button onClick={handleReset} className="hover:text-white text-gray-400 flex items-center gap-1"><RefreshCw size={12}/> 重置</button>)}</div>
      </header>
      <main className={mainClass}>
        {step === 'upload' && (
             <div className="flex-1 flex flex-col items-center justify-start pt-12 md:justify-center md:pt-0 w-full max-w-4xl gap-6 p-6">
                 {pendingProjectData && (
                     <div className="bg-green-900/20 border border-green-500/30 p-3 rounded-lg text-center w-full max-w-sm animate-in fade-in slide-in-from-bottom-4">
                         <div className="flex items-center justify-center gap-2 text-green-400 font-bold text-sm mb-1">
                             <FileJson size={16}/>
                             <span>專案設定已就緒</span>
                         </div>
                         <div className="text-gray-400 text-xs break-all">{pendingProjectData.imageName}</div>
                     </div>
                 )}
                 <div className={`w-full max-w-md aspect-[3/4] border-2 border-dashed rounded-2xl transition-all relative flex flex-col items-center justify-center group cursor-pointer shadow-2xl p-6 ${pendingProjectData ? 'border-green-500/50 bg-green-900/10 hover:bg-green-900/20' : 'border-gray-700 bg-gray-900 hover:border-blue-500'}`}>
                     {pendingProjectData ? (
                        <FileImage size={64} className="text-green-500/80 mb-6 animate-pulse" />
                     ) : (
                        <Upload size={64} className="text-gray-600 group-hover:text-blue-400 mb-6 transition-colors"/>
                     )}
                     <input type="file" accept="image/*,.heic,.heif" onChange={handleImageUpload} className="absolute inset-0 opacity-0 cursor-pointer z-10" />
                     <p className={`font-bold text-xl mb-2 ${pendingProjectData ? 'text-green-400' : 'text-gray-300'}`}>
                         {pendingProjectData ? '請上傳對應圖片' : '上傳卡牌照片'}
                     </p>
                     <p className="text-gray-500 text-sm text-center">
                         {pendingProjectData ? '還原校正與測量數據' : '支援 JPG, PNG, HEIC (確保四角清晰)'}
                     </p>
                 </div>
                 <div className="flex flex-col items-center gap-3">
                     {!pendingProjectData ? (
                         <div className="relative group">
                             <button className="flex items-center gap-2 text-gray-400 group-hover:text-white px-5 py-2.5 rounded-full border border-gray-700 group-hover:border-gray-500 bg-gray-800/50 transition-all text-sm">
                                 <FileJson size={16} />
                                 <span>載入專案設定 (.json)</span>
                             </button>
                             <input type="file" accept=".json" onChange={handleJsonUpload} className="absolute inset-0 opacity-0 cursor-pointer" />
                         </div>
                     ) : (
                         <button onClick={() => setPendingProjectData(null)} className="text-gray-600 hover:text-gray-400 text-xs py-2 transition-colors">
                             取消載入 (返回一般上傳)
                         </button>
                     )}
                 </div>
             </div>
        )}
        {(step === 'crop' || step === 'measure') && (
            <div className={`flex-shrink-0 select-none ${step === 'measure' ? 'max-h-[85vh] overflow-y-auto bg-gray-800 rounded-xl p-2 w-fit max-w-full' : 'relative w-fit h-fit'}`} ref={containerRef}>
                <div className="relative w-fit h-fit">
                    <img ref={imgRef} src={step === 'crop' ? originalImage?.src : processedImage?.src} alt="Work" className="object-contain pointer-events-none shadow-2xl" style={step === 'crop' ? { maxWidth: `${BASE_TARGET_WIDTH}px`, maxHeight: '80vh' } : (processedImage ? { width: `${processedImage.naturalWidth}px`, height: 'auto' } : {})} />
                    {(step === 'crop' || step === 'measure') && (
                        <div className={`fixed right-2 top-1/2 transform -translate-y-1/2 bg-gray-800/90 backdrop-blur-sm rounded-lg shadow-xl z-50 flex flex-col gap-2 border border-gray-700 transition-all duration-300 ${isMagnifierPanelCollapsed ? 'p-2 w-10' : 'p-3'}`}>
                             <button onClick={() => setIsMagnifierPanelCollapsed(!isMagnifierPanelCollapsed)} className="self-end text-gray-400 hover:text-white mb-1 focus:outline-none" title={isMagnifierPanelCollapsed ? "展開" : "收起"}>
                                {isMagnifierPanelCollapsed ? <ChevronLeft size={16}/> : <ChevronRight size={16}/>}
                            </button>
                            {!isMagnifierPanelCollapsed && (
                                <>
                                    <p className="text-xs text-gray-300 font-semibold mb-1 text-center whitespace-nowrap">放大鏡</p>
                                    {zoomOptions.map(z => (<button key={z} onClick={() => handleZoomChange(z)} className={`w-10 h-10 text-xs font-bold rounded-lg transition-all border ${zoomLevel === z ? 'bg-blue-600 text-white shadow-md border-blue-400' : 'bg-gray-700 text-gray-300 hover:bg-gray-600 border-gray-600'}`}>{z.toFixed(1)}X</button>))}
                                    <p className="text-xs text-gray-500 text-center mt-1">1.0X 原圖</p>
                                </>
                            )}
                            {isMagnifierPanelCollapsed && (
                                <div className="flex flex-col items-center gap-1">
                                    <button onClick={cycleZoom} className="text-[10px] font-bold text-blue-400 hover:text-white transition-colors w-full text-center" title="點擊切換倍率">
                                        {zoomLevel.toFixed(1)}X
                                    </button>
                                </div>
                            )}
                        </div>
                    )}
                    {step === 'crop' && originalImage && (
                        <CropOverlay 
                            cropPoints={cropPoints} 
                            getImageContainerRect={getLiveImageRect} 
                            getScreenCoords={getScreenCoords} 
                            activePointIndex={activePointIndex}
                            lastActivePointIndex={lastActivePointIndex} 
                            handleCropDragStart={handleCropDragStart} 
                            imgRef={imgRef} 
                            key={`crop-overlay-${coordsKey}`} 
                        />
                    )}
                    {step === 'measure' && processedImage && (
                        <div 
                            className="absolute inset-0 w-full h-full pointer-events-auto cursor-crosshair"
                            onMouseDown={handleGeneralMouseDown}
                            onTouchStart={handleGeneralTouchStart}
                        > 
                            {renderDraggableLine('outerTop', 'horizontal', 'border-blue-500', false)}
                            {renderDraggableLine('outerBottom', 'horizontal', 'border-blue-500', false)}
                            {renderDraggableLine('outerLeft', 'vertical', 'border-blue-500', false)}
                            {renderDraggableLine('outerRight', 'vertical', 'border-blue-500', false)}
                            {renderDraggableLine('innerTop', 'horizontal', 'border-red-500', true)}
                            {renderDraggableLine('innerBottom', 'horizontal', 'border-red-500', true)}
                            {renderDraggableLine('innerLeft', 'vertical', 'border-red-500', true)}
                            {renderDraggableLine('innerRight', 'vertical', 'border-red-500', true)}
                        </div>
                    )}
                </div>
                {isProcessing && (<div className="fixed inset-0 bg-black/80 z-50 flex flex-col items-center justify-center text-white"><Loader2 className="animate-spin mb-4" size={40}/><p>{loadingText}</p></div>)}
            </div>
        )}
      </main>
      <Magnifier magnifierState={{...magnifier, cropPoints: cropPoints, measureLines: measureLines, currentStep: step}} zoom={zoomLevel} cardImage={cardImageForMagnifier}/>
      <footer className="bg-gray-900 border-t border-gray-800 p-3 shrink-0 z-40">
        <div className="max-w-4xl mx-auto w-full">
            {step === 'crop' && (
                <div className="flex flex-col md:flex-row items-center justify-between gap-3">
                     <div className="flex flex-col gap-1 w-full md:w-auto">
                        <div className="text-gray-400 text-xs md:text-sm"><span className="text-green-400 font-bold">步驟 1:</span> 拖曳四個綠點至卡牌角落</div>
                        <div className="text-gray-500 text-[10px]">點擊任一綠點即可進行微調</div>
                     </div>
                     <div className="flex items-center gap-2 bg-gray-800/50 p-1.5 rounded-lg border border-gray-700">
                         <div className="flex flex-col items-center justify-center gap-1">
                             <button onClick={() => nudgeCropPoint(0, -1)} disabled={lastActivePointIndex === null} className={`w-8 h-8 rounded bg-gray-700 flex items-center justify-center ${lastActivePointIndex !== null ? 'hover:bg-blue-600 text-white' : 'opacity-30 cursor-not-allowed'}`}><ChevronUp size={16}/></button>
                             <div className="flex gap-1">
                                 <button onClick={() => nudgeCropPoint(-1, 0)} disabled={lastActivePointIndex === null} className={`w-8 h-8 rounded bg-gray-700 flex items-center justify-center ${lastActivePointIndex !== null ? 'hover:bg-blue-600 text-white' : 'opacity-30 cursor-not-allowed'}`}><ChevronLeft size={16}/></button>
                                 <div className="w-8 h-8 flex items-center justify-center text-blue-400">
                                     {lastActivePointIndex !== null ? <Move size={16} /> : <MousePointerClick size={16} className="text-gray-600"/>}
                                 </div>
                                 <button onClick={() => nudgeCropPoint(1, 0)} disabled={lastActivePointIndex === null} className={`w-8 h-8 rounded bg-gray-700 flex items-center justify-center ${lastActivePointIndex !== null ? 'hover:bg-blue-600 text-white' : 'opacity-30 cursor-not-allowed'}`}><ChevronRight size={16}/></button>
                             </div>
                             <button onClick={() => nudgeCropPoint(0, 1)} disabled={lastActivePointIndex === null} className={`w-8 h-8 rounded bg-gray-700 flex items-center justify-center ${lastActivePointIndex !== null ? 'hover:bg-blue-600 text-white' : 'opacity-30 cursor-not-allowed'}`}><ChevronDown size={16}/></button>
                         </div>
                         <div className="text-[10px] text-gray-500 w-24 text-center leading-tight">
                             {activePt ? (
                                 <>
                                    <div>微調選中點</div>
                                    <div className="font-mono text-xs text-blue-300">
                                        {`X:${(activePt.x * 100).toFixed(1)}% Y:${(activePt.y * 100).toFixed(1)}%`}
                                    </div>
                                 </>
                             ) : '請先點選綠點'}
                         </div>
                     </div>
                     <button onClick={performWarpAndProceed} className="bg-green-600 hover:bg-green-500 text-white px-6 py-2 rounded-full font-bold shadow-lg flex items-center gap-2 active:scale-95 transition-all w-full md:w-auto justify-center">校正並繼續 <ArrowRight size={18}/></button>
                </div>
            )}
            {step === 'measure' && (
                <div className="flex flex-col gap-3">
                    <div className="flex items-center justify-between"><button onClick={handleBackToCrop} className="text-gray-500 hover:text-white px-2 py-1 flex items-center gap-1 text-xs"><ArrowLeft size={14}/> 重調四角 (保留上次位置)</button><div className="flex items-center gap-2"><button onClick={() => nudgeLine(-1)} disabled={!selectedLineId} className={`w-10 h-10 rounded-full flex items-center justify-center border transition-colors ${selectedLineId ? 'bg-gray-800 hover:bg-gray-700 border-gray-700 text-white' : 'bg-gray-900 border-gray-800 text-gray-600 cursor-not-allowed'}`}>{(selectedLineId?.includes('Top') || selectedLineId?.includes('Bottom')) ? <ChevronUp size={20}/> : <ChevronLeft size={20}/>}</button><div className="text-center w-24"><div className="text-[10px] text-gray-500 uppercase tracking-wider">微調</div><div className="text-xs font-bold text-blue-300 truncate">{selectedLineId ? (<><div>{selectedLineId.includes('outer') ? '藍線 (卡邊)' : '紅線 (圖案)'}</div><div>{measureLines[selectedLineId].toFixed(2)}%</div></>) : '請點選虛線'}</div></div><button onClick={() => nudgeLine(1)} disabled={!selectedLineId} className={`w-10 h-10 rounded-full flex items-center justify-center border transition-colors ${selectedLineId ? 'bg-gray-800 hover:bg-gray-700 border-gray-700 text-white' : 'bg-gray-900 border-gray-800 text-gray-600 cursor-not-allowed'}`}>{(selectedLineId?.includes('Top') || selectedLineId?.includes('Bottom')) ? <ChevronDown size={20}/> : <ChevronRight size={20}/>}</button></div><div className="flex justify-end gap-2"><button onClick={handleExportJSON} className="bg-blue-600 hover:bg-blue-500 text-white p-2 rounded-lg shadow-sm transition-colors" title="儲存專案檔 (.json)"><FileJson size={20}/></button><button onClick={downloadResultImage} className="bg-emerald-600 hover:bg-emerald-500 text-white p-2 rounded-lg shadow-sm transition-colors" title="下載結果圖 (.png)"><ImageIcon size={20}/></button></div></div>
                    <div className="bg-black/40 rounded-lg p-2 flex items-center justify-around border border-gray-700"><div className="flex flex-col items-center w-1/2 border-r border-gray-700"><span className="text-[10px] text-gray-400 uppercase">左右比例 (H)</span><div className="flex items-baseline gap-1"><span className={`text-lg font-bold ${Math.abs(results.h.left - results.h.right) <= 10 ? 'text-green-400' : 'text-yellow-400'}`}>{results.h.left.toFixed(1)} : {results.h.right.toFixed(1)}</span></div></div><div className="flex flex-col items-center w-1/2"><span className="text-[10px] text-gray-400 uppercase">上下比例 (V)</span><div className="flex items-baseline gap-1"><span className={`text-lg font-bold ${Math.abs(results.v.top - results.v.bottom) <= 10 ? 'text-green-400' : 'text-yellow-400'}`}>{results.v.top.toFixed(1)} : {results.v.bottom.toFixed(1)}</span></div></div></div>
                </div>
            )}
        </div>
      </footer>
    </div>
  );
}

const CropOverlay = ({ cropPoints, renderedImageRect, getScreenCoords, activePointIndex, lastActivePointIndex, handleCropDragStart, imgRef, getImageContainerRect }) => {
    // 確保這裡使用正確的 rect 獲取方式
    const containerRect = getImageContainerRect ? getImageContainerRect() : (imgRef.current?.getBoundingClientRect() || renderedImageRect);
    
    if (!containerRect || containerRect.width === 0) return null;
    
    // 計算螢幕座標 (僅用於 SVG 多邊形，因為 SVG 需要絕對像素值)
    const screenPoints = cropPoints.map(p => { 
        const c = getScreenCoords(p.x, p.y); 
        return { c, p, originalIndex: cropPoints.indexOf(p) }; 
    });
    
    if (screenPoints.length !== 4) return null; 
    
    // SVG 點位 (使用像素座標)
    const polygonPoints = screenPoints.map(item => `${item.c.x - containerRect.left},${item.c.y - containerRect.top}`).join(' ');

    return (
        <>
            <svg className="absolute inset-0 w-full h-full pointer-events-none">
                <polygon points={polygonPoints} fill="rgba(34, 197, 94, 0.1)" stroke="rgba(34, 197, 94, 0.8)" strokeWidth="2" strokeDasharray="5" />
            </svg>
            {screenPoints.map((item, i) => {
                const isActive = activePointIndex === item.originalIndex;
                const isSelected = lastActivePointIndex === item.originalIndex;
                
                // *** 關鍵修復 ***
                // 這裡改用 percentage (%) 定位，並且設為 absolute
                // 這樣拖動點就會相對於圖片容器定位，滾動時會緊貼圖片
                const leftPct = `${item.p.x * 100}%`;
                const topPct = `${item.p.y * 100}%`;

                // Add touch-action: none to prevent browser gestures on the point itself
                const styleWithTouch = { left: leftPct, top: topPct, touchAction: 'none' };

                return (
                    <div 
                        key={item.originalIndex} 
                        className={`absolute w-8 h-8 -ml-4 -mt-4 rounded-full border-2 cursor-move flex items-center justify-center shadow-[0_0_10px_rgba(0,0,0,0.5)] pointer-events-auto transition-transform ${isActive ? 'bg-green-400 border-white scale-125 z-30' : (isSelected ? 'bg-green-500 border-yellow-400 z-25 scale-110 shadow-[0_0_10px_rgba(250,204,21,0.6)]' : 'bg-green-500/80 border-green-200 z-20')}`} 
                        style={styleWithTouch} 
                        onMouseDown={(e) => handleCropDragStart(item.originalIndex, e)} 
                        onTouchStart={(e) => handleCropDragStart(item.originalIndex, e)}
                    >
                        <Move size={14} className={isSelected ? "text-yellow-100" : "text-black"} />
                    </div>
                );
            })}
        </>
    );
};

export default function App() {
    return (
        <CardGraderTool />
    )
}